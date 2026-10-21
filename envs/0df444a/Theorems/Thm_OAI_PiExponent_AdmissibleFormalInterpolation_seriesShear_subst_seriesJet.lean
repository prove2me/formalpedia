-- Prove2me | Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_seriesShear_subst_seriesJet
-- name    : OAI.PiExponent.AdmissibleFormalInterpolation.seriesShear_subst_seriesJet
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-17T22:21:18.63501+00:00
-- url     : https://prove2.me/theorems/d9a364f6-7b47-4da7-8829-3eb3dc403eb4
-- title:
--   Admissible formal shear composes with polynomial series jets
-- statement:
--   When every D_i has zero constant coefficient, formal shear substitution sends the polynomial series jet formed using F to the jet formed using F+D. The background family F may have arbitrary constant terms.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_WeightedJetShear
import Mathlib.RingTheory.MvPowerSeries.Substitution

open OAI.PiExponent OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.AdmissibleFormalInterpolation.seriesShear_subst_seriesJet
    {m : ℕ} (D F : Fin m → PowerSeries ℂ) (c : Fin m → ℂ)
    (hD0 : ∀ i, PowerSeries.coeff 0 (D i) = 0)
    (P : MvPolynomial (Fin (m + 1)) ℂ) :
    MvPowerSeries.subst
        (Fin.cases (MvPowerSeries.X 0)
          (fun i => MvPowerSeries.X i.succ + liftLogSeries m (D i)))
        (seriesJet c F P) =
      seriesJet c (fun i => F i + D i) P := by sorry
