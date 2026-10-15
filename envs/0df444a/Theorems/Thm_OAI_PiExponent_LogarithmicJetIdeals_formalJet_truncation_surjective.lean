-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_truncation_surjective
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_truncation_surjective
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T05:27:30.899795+00:00
-- url     : https://prove2.me/theorems/e2a8e5ab-922c-4b6b-83dd-ace8b0d84fc0
-- title:
--   Surjectivity of finite truncations of the formal logarithmic jet
-- statement:
--   For any polynomial and any strict total-degree cutoff, some polynomial’s formal logarithmic jet agrees with the given polynomial’s power series at every multi-index below that cutoff.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_truncation_surjective
    {m : ℕ} (center : Fin m → ℂ)
    (R : MvPolynomial (Fin (m + 1)) ℂ) (T : ℕ) :
    ∃ Q : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ d : Fin (m + 1) → ℕ,
        (∑ i, d i) < T →
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
          (formalJet center Q) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
          (MvPolynomial.toMvPowerSeries R) := by sorry
