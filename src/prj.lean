/-
-/
import tactic
import data.real.basic
import data.set.intervals.basic
import algebra.order.floor

namespace set

variables (a b : ℝ)

def I := {x : ℝ // x ∈ Icc a b}

def Itendsto (s : ℕ → I a b) (t : I a b) : Prop :=
∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |(s n).val - t.val| < ε

def Rtendsto (s : ℕ → ℝ) (t : ℝ) : Prop := 
∀ ε > 0, ∃ B : ℕ, ∀ n, B ≤ n → |s n - t| < ε 

def I_continuity (f : I a b → ℝ) (x : I a b) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ y : I a b, |x.val - y.val| < δ → |f x - f y| < ε

example (n : ℕ) : (1 : ℝ) / (n + 1) > 0 :=
begin
  exact nat.one_div_pos_of_nat,
end

lemma I_cont_sql_cont1 {a b : ℝ} {f : I a b → ℝ} {x : I a b}:
  I_continuity a b f x ↔ ∀ (s : {seq : ℕ → I a b // Itendsto a b seq x}), Rtendsto (f ∘ s) (f x) :=

  begin
    split,
    intros hc s ε hε,
    cases hc ε hε with δ,
    cases h with hδ,
    cases s.property δ hδ with N,
    use N,
    intros n hn, 
    suffices hs1 : |f x - f (s.val n)| < ε,
      dsimp,
      rw abs_sub_comm,
      exact hs1,
    suffices : |x.val - (s.val n).val| < δ,
      exact h_h (s.val n) this,
    rw abs_sub_comm x.val (s.val n).val,
    exact h n hn,

    intros s,
    unfold I_continuity,
    intros ε hε,
    by_contra,
    push_neg at h,
    let sn : ℕ → ℝ := λ n, (1 : ℝ) / (n + (1 : ℝ)),
    have h₁ : ∀ (n : ℕ), ∃ (y : I a b), |x.val - y.val| < sn n ∧ ε ≤ |f x - f y|,
      intros n,
      exact h (sn n) nat.one_div_pos_of_nat,
    choose tn htn using h₁,
    have h₂ : Itendsto a b tn x,
      intros ε1 hε1, 
      use ⌈1/ε1⌉₊, 
      intros n hn,
      rw abs_sub_comm (tn n).val x.val,
      suffices : sn n < ε1,
        calc |x.val - (tn n).val| < sn n : (htn n).1
                              ... < ε1   : this,
      have s1 : ⌈1 / ε1⌉₊ < n + 1, 
        by linarith,
      have s2 : (1 / ε1) < n + 1, 
        exact nat.lt_of_ceil_lt s1,
      have s3 : (n + 1 : ℝ) > 0,
        exact nat.cast_add_one_pos n,
      have s4 : 1 / (n + 1 : ℝ) < 1 / (1/ ε1),
        exact (one_div_lt_one_div s3 (one_div_pos.mpr hε1)).mpr s2,
      calc sn n < 1 / (1 / ε1) : s4
            ... = ε1            : by norm_num,

    specialize s ⟨tn, h₂⟩,
    cases s ε hε with N,
    specialize h_1 (N+1) (by norm_num),
    specialize htn (N+1),
    simp at h_1,
    have h₃ : |f x - f (tn (N + 1))| < ε,
      calc |f x - f (tn (N + 1))| = |f (tn (N + 1)) - f x| : abs_sub_comm (f x) (f (tn (N + 1)))
                              ... < ε                      : h_1,
    have h₄ : ε ≤ |f x - f (tn (N + 1))|,
      exact htn.2,
    linarith,


  end

end set

