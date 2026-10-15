-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_subst_inverse_shear
-- name    : OAI.PiExponent.LogarithmicJetIdeals.subst_inverse_shear
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-14T23:14:17.238371+00:00
-- url     : https://prove2.me/theorems/f5631337-fed6-4eb3-ab44-27db0596d28a
-- title:
--   Inverse substitution cancels a formal shear
-- statement:
--   For any family of formal power series, substituting each variable by itself minus its lifted series after evaluating a polynomial at the variables plus those same lifted series recovers the polynomial evaluated at the power-series variables.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.subst_inverse_shear
    {m : ℕ} (D : Fin m → PowerSeries ℂ)
    (Q : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPowerSeries.subst
      (Fin.cases (MvPowerSeries.X 0)
        (fun i => MvPowerSeries.X i.succ - liftLogSeries m (D i)))
      (MvPolynomial.aeval
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))) Q) =
    MvPolynomial.aeval MvPowerSeries.X Q := by sorry
