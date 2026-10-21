-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_shear_roundtrip_series
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_roundtrip_series
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T05:49:28.993888+00:00
-- url     : https://prove2.me/theorems/42f525c5-0cbd-449e-9eba-e426127f4a28
-- title:
--   Weighted hypotheses make inverse shear recover the evaluated polynomial
-- statement:
--   Under the parent's positivity and weighted coefficient-vanishing hypotheses, applying the inverse shear to the polynomial evaluated at the forward shear recovers its evaluation at the identity variables.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_roundtrip_series
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (D : Fin m → PowerSeries ℂ)
    (hD : ∀ i : Fin m, ∀ n : ℕ,
      (n : ℝ) * q 0 < q i.succ → PowerSeries.coeff n (D i) = 0)
    (Q : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPowerSeries.subst
      (Fin.cases (MvPowerSeries.X 0)
        (fun i => MvPowerSeries.X i.succ - liftLogSeries m (D i)))
      (MvPolynomial.aeval
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))) Q) =
    MvPolynomial.aeval MvPowerSeries.X Q := by sorry
