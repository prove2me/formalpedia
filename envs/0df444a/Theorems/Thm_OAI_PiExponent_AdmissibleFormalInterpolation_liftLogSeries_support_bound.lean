-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_liftLogSeries_support_bound
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_support_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T05:52:45.051907+00:00
-- url     : https://prove2.me/theorems/fc8dc4cd-dbda-4ea8-b255-ea50d62b8a78
-- title:
--   Tail-series support satisfies the cutoff weight bound
-- statement:
--   A nonzero coefficient of the lifted univariate tail has no exponents outside coordinate 0, and its degree k cannot be below T i. Positivity of q 0 and the cutoff inequality therefore give the required weighted lower bound.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.MvPowerSeries.Substitution

open scoped BigOperators
open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.liftLogSeries_support_bound
    {m : ℕ} (q : Fin (m + 1) → ℝ) (T : Fin m → ℕ)
    (R : Fin m → PowerSeries ℂ)
    (hq : ∀ i, 0 < q i)
    (hT : ∀ i : Fin m, q i.succ ≤ (T i : ℝ) * q 0)
    (hR : ∀ (i : Fin m) (k : ℕ), k < T i → PowerSeries.coeff k (R i) = 0)
    (i : Fin m) (a : Fin (m + 1) → ℕ) :
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector a)
      (liftLogSeries m (R i)) ≠ 0 →
    q i.succ ≤ ∑ j, q j * (a j : ℝ) := by sorry
