/-
-/
import tactic
import data.real.basic
import data.set.intervals.basic
import algebra.order.floor

variables (a b : ℝ)
open set 
def I := {x : ℝ // x ∈ Icc a b}

/-Defines convegences for sequences on I a b-/
def Itendsto (s : ℕ → I a b) (t : I a b) : Prop :=
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |(s n).val - t.val| < ε

/-Defines convergence for sequences on ℝ-/
def Rtendsto (s : ℕ → ℝ) (t : ℝ) : Prop := 
  ∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |s n - t| < ε 

/-Defines pointwise continuity for a point of type I a b-/
def I_pt_continuity (f : I a b → ℝ) (x : I a b) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y : I a b, |x.val - y.val| < δ → |f x - f y| < ε

/-Defines the property of continuity for type I a b-/
def I_continuity (f : I a b → ℝ) : Prop :=
  ∀ (x : I a b), I_pt_continuity a b f x

/-For f on I a b, pointwise continuity at x is equivalent to sequential continuity at that point.-/
lemma I_cont_sql_cont_pt (a b : ℝ) (f : I a b → ℝ) (x : I a b):
I_pt_continuity a b f x ↔ ∀ (s : {seq : ℕ → I a b // Itendsto a b seq x}), Rtendsto (f ∘ s) (f x) :=
begin
  /-Separate right and left implication-/
  split,
  /-Forward case is fairly simple, for sequence s with ε > 0, find δ neighbourhood s.t. the image
      of this neighbourhood is within ε of f x. Then find sufficiently large N s.t. s is in the neighbourhood.-/
    /-Intro continuity property, sequence s and ε-/
    intros hcontin s ε hε,
    /-Extract δ neighbourhood with δ > 0.-/
    cases hcontin ε hε with δ,
    cases h with hδ,
    /-Extract N large enough s.t. s is in the δ neighbourhood above N.-/
    cases s.property δ hδ with N,
    use N,
    intros n hn,
    /-Adapt goal slightly.-/
    suffices hs1 : |f x - f (s.val n)| < ε,
      dsimp,
      rw abs_sub_comm,
      exact hs1,
    /-Show its sufficient that s is in the δ neighbourhood.-/
    suffices : |x.val - (s.val n).val| < δ,
      exact h_h (s.val n) this,
    rw abs_sub_comm x.val (s.val n).val,
    /-Goal is exactly the earlier proof that s is in the δ neighbourhood.-/
    exact h n hn,
  
  /-Backwards case proceeds by assuming the goal is not true and finding a
    sequence tn s.t. tn → x but f tn doesnt tend to f x. -/
    /-intros ε > 0.-/
    intros s,
    intros ε hε,
    /-intros negation of goal to find contradiction.-/
    by_contra,
    push_neg at h,
    /-define sequence we'll bound our target sequence with.-/
    let sn : ℕ → ℝ := λ n, (1 : ℝ) / (n + (1 : ℝ)),
    /-obtain sequence tn which converges to x, at least ε from f x-/
    have h₁ : ∀ (n : ℕ), ∃ (y : I a b), |x.val - y.val| < sn n ∧ ε ≤ |f x - f y|,
      intros n,
      exact h (sn n) nat.one_div_pos_of_nat,
    choose tn htn using h₁,
    /-show tn converges to x in I a b.-/
    have h₂ : Itendsto a b tn x,
      intros ε1 hε1,
      /-will choose a val greater than 1/ε1, then bound |tn - x| by sn val -/
      use ⌈1/ε1⌉₊, 
      intros n hn,
      rw abs_sub_comm (tn n).val x.val,
      /-show its sufficient to show sn < ε1-/
      suffices : sn n < ε1,
        calc |x.val - (tn n).val| < sn n : (htn n).1
                              ... < ε1   : this,
      /-show that sn n ≤ ε1-/
      have s1 : ⌈1 / ε1⌉₊ < n + 1, 
        by linarith,
      have s2 : (1 / ε1) < n + 1, 
        exact nat.lt_of_ceil_lt s1,
      have s3 : (n + 1 : ℝ) > 0,
        exact nat.cast_add_one_pos n,
      have s4 : 1 / (n + 1 : ℝ) < 1 / (1/ ε1),
        exact (one_div_lt_one_div s3 (one_div_pos.mpr hε1)).mpr s2,
      calc sn n < 1 / (1 / ε1) : s4
            ... = ε1           : by norm_num,
    /-obtain proof that f ∘ tn converges to f x-/
    specialize s ⟨tn, h₂⟩,
    /-intro sufficiently large N s.t. above it, f ∘ tn is in ε of f x -/
    cases s ε hε with N,
    /-specifiy above to N + 1-/
    specialize h_1 (N+1) (by norm_num),
    simp at h_1,
    /-rw into a different form for simplicity-/
    have h₃ : |f x - f (tn (N + 1))| < ε,
      calc |f x - f (tn (N + 1))| = |f (tn (N + 1)) - f x| : abs_sub_comm (f x) (f (tn (N + 1)))
                              ... < ε                      : h_1,
    /-specify f tn being distance ε away from f x for N + 1-/
    specialize htn (N+1),
    /-induce contradiction from last 2 inequalities-/
    linarith [htn.2, h₃],
end

/-Intermediate value theorem for continuous f on I a b-/
lemma intermed_val {a b : ℝ} {a < b} {f : I a b → ℝ} {h₁ : I_continuity a b f}:
  ∀ (y : I (f ⟨a,⟨by linarith, by linarith⟩⟩) (f ⟨b, ⟨by linarith, by linarith⟩⟩)), ∃ (x₁ : I a b), f (x₁) = y.val := 
begin
  sorry,
end

/-Bolzano-Weirstrass for a sequence on I a b-/
lemma bolz_weir_I (a b : ℝ) (sn : ℕ → I a b):
  ∃ (c : I a b), ∃ (tn : ℕ → ℕ), strict_mono tn ∧ Itendsto a b (sn ∘ tn) c :=
begin
  sorry,
end 

/-Natural ceil of a real + a nat is less than the real nat ceil plus the nat.-/
lemma  nat_ceil (var : ℝ) (n : ℕ)  : 
⌈var + n⌉₊ ≤ ⌈var⌉₊ + n :=
begin
  /-split into cases -/
  by_cases var ≤ -(n : ℝ),
  calc ⌈var + n⌉₊ = (0 : ℕ)   : nat.ceil_eq_zero.mpr (show var + n ≤ 0, by linarith) 
              ... = ⌈var⌉₊     : by linarith [nat.ceil_eq_zero.mpr (show var ≤ 0, by linarith [(show -(n : ℝ) ≤ 0, by simp)] )]
              ... ≤ ⌈var⌉₊ + n : by linarith,
  push_neg at h,
  /-show its sufficient that the inequality coerced to the reals is true.-/
  suffices : (⌈var + ↑n⌉₊ : ℝ) ≤ ↑(⌈var⌉₊ + n),
    /-non-working attempt:
    exact nat.coe_nat_le.mp this,-/
    sorry,

  /-prove the inequality coerced to the reals is true.-/
  /- non-working attempt, struggled with the typing:
  calc (⌈var + ↑n ⌉₊ : ℝ) = ↑⌈var + n⌉       : nat.cast_ceil_eq_cast_int_ceil (by linarith)
              ... = ⌈var⌉ + ↑↑n            : by rw (int.ceil_add_int var n)
              ... ≤ ⌈var⌉₊ + n              : by linarith [(show ⌈var⌉ = ⌈var⌉₊, by refl)]-/
  sorry,
end

lemma I_cont_bdd {a b : ℝ} {f : I a b → ℝ} :
I_continuity a b f → ∃ (M : ℝ), ∀ (x : I a b), |f x| < M :=
begin
  intros h₁,
  /-Show its sufficient to show f is bounded from above and below.-/
  /-bound f from above and below.-/
  suffices goal1 : ∃ (M1 : ℝ), ∀ (x : I a b), f x < M1,
    suffices goal2 : ∃ (M2 : ℝ), ∀ (x : I a b), M2 < f x,
      /-extract upper and lower bound for f.-/
      cases goal1 with M1,
      cases goal2 with M2,
      /-use max of modulus of upper and lower bounds.-/
      use max M1 (-M2),
      /-intro arbitrary x, rw goal to 2 conditions.-/
      intros x,
      rw abs_lt,
      /-apply bound to f x.-/
      specialize goal1_h x,
      specialize goal2_h x,
      /-split ∧ in goal into 2 separate goals -/
      split, 
      have :  ∀ ( a b : ℝ), -max a b ≤ -b, norm_num,
      /-show f x bounded below by our choice-/
      calc (-max M1 (-M2)) ≤ -(-M2)   : this M1 (-M2)
                      ... = M2        : by ring
                      ... < f x       : goal2_h,
    /-show f x is bounded above by our choice-/
    calc f x < M1                  : goal1_h
        ... ≤ max M1 (-M2)        : by norm_num,
  /-only focus on bounding f from above for now.-/
  sorry,
  /-intro negation of goal to prove by contradiction-/
  by_contra,
  push_neg at h,
  /-construct sequence we'll bound f tn by from below.-/
  let sn : ℕ → ℝ := λ n, n,
  have hcons : ∀ (n : ℕ), ∃ (x : I a b), sn n ≤ f x,
    intros n,
    exact h (sn n),
  /-extract sequence tn using above s.t. n ≤ tn -/
  choose tn htn using hcons,
  /-extract subsequence of tn s.t. it converges using bolzanno-weierstrass.-/
  cases (bolz_weir_I a b tn) with c,
  cases h_1 with qn,
  /-find sufficient N s.t. f ∘ tn ∘ qn is within 1 of f c-/
  have main : Rtendsto (f ∘ tn ∘ qn) (f c),
    exact (I_cont_sql_cont_pt a b f c).mp (h₁ c) ⟨(tn ∘ qn), h_1_h.right⟩,
  specialize main 1 (by linarith),
  cases main with N,
  /-specialise to n = N of above.-/
  have main1 : |f (tn ( qn N)) - f c| < 1,
    exact main_h N (by linarith),

  /-specialise main to n = ⌈f (tn (qn N))⌉₊ + 2, which will lead to contradiction.-/
  have : N ≤ ⌈f (tn (qn N))⌉₊ + 2,
    sorry,
  have main2 : |f (tn ( qn (⌈f (tn (qn N))⌉₊ + 2))) - f c| < 1,
    exact main_h (⌈f (tn (qn N))⌉₊ + 2) this,
  
  /-bound f c from above by f( tn( qn N) + 1-/
  have main3 : f c < f ( tn( qn N)) + 1,
    rw abs_lt at main1,
    linarith [main1.left],

  /-bound f c + 1 below.-/
  have main4 : f (tn (qn (⌈f (tn (qn N))⌉₊ + 2))) < f c + 1,
    rw abs_lt at main2,
    linarith [main2.right],

  /-show f c + 1 is bounded below by f(tn (qn N)):
    -find N greater than f(tn(qn N)) using ⌈ ⌉₊
    -use monotonicity of qn and identity of sn
    -use f bounded below by sn
    -use earlier result that this is bounded above by f c + 1.apply.
  -/
  have this1 : ⌈f(tn (qn N)) + ↑2⌉₊ ≤ ⌈f(tn (qn N))⌉₊ + 2, exact nat_ceil (f (tn (qn N))) 2,
  have main5 : f (tn (qn N)) + 2 < f c + 1, 
    calc f(tn (qn N)) + 2 ≤ ↑⌈f(tn (qn N)) + (2 : ℝ)⌉₊  : nat.le_ceil (f (tn (qn N)) + 2)
                      ... ≤ ↑(⌈f(tn (qn N))⌉₊ + 2)      : sorry /-nat.cast_le.mpr (nat_ceil (f (tn (qn N))) 2)-/
                      ... = ↑⌈f(tn (qn N))⌉₊ + (2 : ℝ)  : by simp
                      ... ≤ ↑(qn(⌈f(tn (qn N))⌉₊ + 2))  : sorry /-(function.well_founded.self_le_of_strict_mono (nat.lt_wf) h_1_h.left (⌈f(tn (qn N))⌉₊ + 2))-/
                      ... = sn (qn (⌈f (tn (qn N))⌉₊ + 2)) : rfl
                      ... ≤ f (tn ((qn (⌈f (tn (qn N))⌉₊ + 2)))) : htn (qn (⌈f (tn (qn N))⌉₊ + 2))
                      ... < f c + 1                           : main4,
  /-derive contradiction from above and below bound of f c by f tn qn N + 1.-/
  linarith,
end 


