-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formal_jet_interpolation_of_injective_requests
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formal_jet_interpolation_of_injective_requests
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-13T23:06:12.165833+00:00
-- url     : https://prove2.me/theorems/bbe9c705-c8a1-46cd-a474-193dd473e546
-- title:
--   Interpolation for injective formal jet requests
-- statement:
--   Given a finite family of requests at arbitrary complex center vectors, each specifying one formal-jet coefficient, any values can be interpolated by a polynomial provided no center/exponent pair is repeated.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.formal_jet_interpolation_of_injective_requests
    {m : ℕ} {ι : Type} [Fintype ι]
    (c : ι → Fin m → ℂ)
    (exponent : ι → (Fin (m + 1) →₀ ℕ))
    (values : ι → ℂ)
    (hindex : Function.Injective (fun x => (c x, exponent x))) :
    ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ x, MvPowerSeries.coeff (exponent x)
        (OAI.PiExponent.AdmissibleFormalInterpolation.formalJet (c x) P) = values x := by sorry
