-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_finite_formal_jet_interpolation
-- name    : OAI.PiExponent.LogarithmicJetIdeals.finite_formal_jet_interpolation
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-13T21:58:48.636587+00:00
-- url     : https://prove2.me/theorems/f8eb26ef-25ae-4c5a-91b1-41746aed483b
-- title:
--   Finite interpolation of formal logarithmic jets
-- statement:
--   For a finite family of logarithmic jet coefficient requests, every assignment of complex values is realized by a polynomial when no center/exponent pair is repeated and the centers are distinct.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals

theorem OAI.PiExponent.LogarithmicJetIdeals.finite_formal_jet_interpolation
    {m : ℕ} {ι : Type} [Fintype ι]
    (K : ℕ) (r : Fin m → ℂ)
    (center : ι → Fin K)
    (exponent : ι → (Fin (m + 1) →₀ ℕ))
    (values : ι → ℂ)
    (hcenters : Function.Injective (fun j : Fin K => fun i : Fin m => (j.val : ℂ) * r i))
    (hindex : Function.Injective (fun x => (center x, exponent x))) :
    ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ x, MvPowerSeries.coeff (exponent x)
        (OAI.PiExponent.AdmissibleFormalInterpolation.formalJet
          (fun i => ((center x).val : ℂ) * r i) P) = values x := by
  sorry
