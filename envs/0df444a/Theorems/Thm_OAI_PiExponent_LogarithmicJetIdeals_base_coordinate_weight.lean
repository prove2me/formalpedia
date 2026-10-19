-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_base_coordinate_weight
-- name    : OAI.PiExponent.LogarithmicJetIdeals.base_coordinate_weight
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T21:39:02.046692+00:00
-- url     : https://prove2.me/theorems/00974c01-58d6-46a2-b53f-dc1487847ec0
-- title:
--   Base shear coordinate coefficients meet their weight
-- statement:
--   Every nonzero coefficient of the base coordinate `X 0` has weight at least its assigned weight `q 0`. Its only nonzero coefficient is at the degree-one monomial, where the weight is exactly `q 0`.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.base_coordinate_weight
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (b : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff b (MvPowerSeries.X 0) ≠ 0 →
      q 0 ≤ ∑ j, q j * (b j : ℝ) := by sorry
