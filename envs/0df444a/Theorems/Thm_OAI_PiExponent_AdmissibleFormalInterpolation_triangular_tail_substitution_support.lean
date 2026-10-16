-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_triangular_tail_substitution_support
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.triangular_tail_substitution_support
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-16T05:47:06.088317+00:00
-- url     : https://prove2.me/theorems/98dd8115-fb3a-4019-8c46-0cc2f7b83d9e
-- title:
--   Triangular tail substitutions satisfy the weighted support bound
-- statement:
--   Under the positive-weight, cutoff, and tail-vanishing hypotheses, every exponent appearing in a substituted variable has weighted degree at least the weight of that variable. For the initial variable this follows from its image being `X 0`; for each other variable it follows from the identity term and the tail cutoff.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.MvPowerSeries.Substitution

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.triangular_tail_substitution_support
    {m : ℕ} (q : Fin (m + 1) → ℝ) (T : Fin m → ℕ)
    (R : Fin m → PowerSeries ℂ)
    (hq : ∀ i, 0 < q i)
    (hT : ∀ i : Fin m, q i.succ ≤ (T i : ℝ) * q 0)
    (hR : ∀ (i : Fin m) (k : ℕ), k < T i → PowerSeries.coeff k (R i) = 0) :
    ∀ (i : Fin (m + 1)) (a : Fin (m + 1) → ℕ),
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
        (Fin.cases (MvPowerSeries.X 0)
          (fun j : Fin m => MvPowerSeries.X j.succ + liftLogSeries m (R j)) i) ≠ 0 →
      q i ≤ ∑ j, q j * (a j : ℝ) := by sorry
