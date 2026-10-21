-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_weighted_shear_coordinate_roundtrip
-- name    : OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_coordinate_roundtrip
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-16T05:58:21.0395+00:00
-- url     : https://prove2.me/theorems/e679eccc-3248-40d9-badc-baebc89ed262
-- title:
--   Weighted hypotheses validate the shear and recover each coordinate
-- statement:
--   The weighted coefficient vanishing makes both shear assignments admissible substitutions, and inverse substitution sends every forward-sheared coordinate back to its original variable.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent
open OAI.PiExponent.AdmissibleFormalInterpolation
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.weighted_shear_coordinate_roundtrip
    {m : ℕ} (q : Fin (m + 1) → ℝ) (hq : ∀ j, 0 < q j)
    (D : Fin m → PowerSeries ℂ)
    (hD : ∀ i : Fin m, ∀ n : ℕ,
      (n : ℝ) * q 0 < q i.succ → PowerSeries.coeff n (D i) = 0) :
    MvPowerSeries.HasSubst
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i))) ∧
      MvPowerSeries.HasSubst
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ - liftLogSeries m (D i))) ∧
      (fun j => MvPowerSeries.subst
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ - liftLogSeries m (D i)))
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i)) j)) =
        MvPowerSeries.X := by sorry
