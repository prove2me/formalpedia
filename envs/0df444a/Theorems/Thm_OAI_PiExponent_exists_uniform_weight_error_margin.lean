-- Prove2me | Theorems.Thm_OAI_PiExponent_exists_uniform_weight_error_margin
-- name    : OAI.PiExponent.exists_uniform_weight_error_margin
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-09T09:15:54.274017+00:00
-- url     : https://prove2.me/theorems/37f56c07-4dea-4b47-918f-e67fb2624044
-- title:
--   A uniform margin for weighted reciprocal sums
-- statement:
--   Let $m$ be a natural number, $\Lambda,\epsilon>0$ real numbers, and $S\ge0$ a real number. There exists $X\ge1$ such that, for every real $w_\star>X$ and every real family $(w_i)_{0\le i<m}$ with $w_i\ge w_\star$ for all $i$,
--
--   $$\Lambda\sum_{i=0}^{m-1}\frac1{w_i}+\frac S{w_\star}<\epsilon.$$
--
--   The same threshold applies to every family with the stated common lower bound, including the empty family when $m=0$.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/WeightErrorMargin.lean#L33-L49

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic

section


namespace OAI

namespace PiExponent

theorem exists_weight_error_margin
    (m : ℕ) (Λ S ε : ℝ) (_hΛ : 0 < Λ) (_hS : 0 ≤ S) (hε : 0 < ε) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ wstar : ℝ, X < wstar →
      Λ * (m : ℝ) / wstar + S / wstar < ε := by
  refine ⟨max 1 ((Λ * (m : ℝ) + S) / ε), le_max_left _ _, ?_⟩
  intro wstar hwstar
  have hwpos : 0 < wstar :=
    lt_of_lt_of_le zero_lt_one (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hwstar))
  have hquot : (Λ * (m : ℝ) + S) / ε < wstar :=
    lt_of_le_of_lt (le_max_right _ _) hwstar
  have hnum : Λ * (m : ℝ) + S < ε * wstar := by
    simpa only [mul_comm] using (div_lt_iff₀ hε).mp hquot
  rw [← add_div]
  exact (div_lt_iff₀ hwpos).mpr hnum

theorem reciprocal_sum_le_common_bound
    (m : ℕ) (w : Fin m → ℝ) (wstar : ℝ) (hwpos : 0 < wstar)
    (hw : ∀ i, wstar ≤ w i) :
    (∑ i : Fin m, 1 / w i) ≤ (m : ℝ) / wstar := by
  calc
    (∑ i : Fin m, 1 / w i) ≤ ∑ _i : Fin m, 1 / wstar := by
      apply Finset.sum_le_sum
      intro i _
      exact one_div_le_one_div_of_le hwpos (hw i)
    _ = (m : ℝ) / wstar := by simp [div_eq_mul_inv]





end PiExponent

end OAI

end

theorem OAI.PiExponent.exists_uniform_weight_error_margin
    (m : ℕ) (Λ S ε : ℝ) (hΛ : 0 < Λ) (hS : 0 ≤ S) (hε : 0 < ε) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ (wstar : ℝ) (w : Fin m → ℝ),
      X < wstar → (∀ i, wstar ≤ w i) →
      Λ * (∑ i : Fin m, 1 / w i) + S / wstar < ε := by sorry
