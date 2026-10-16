-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_coeff_algHom_congr_below_totalDegree
-- name    : OAI.PiExponent.LogarithmicJetIdeals.coeff_algHom_congr_below_totalDegree
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-15T05:41:07.022728+00:00
-- url     : https://prove2.me/theorems/4ac9d6bd-b061-4d0c-997c-c19129e934a2
-- title:
--   Low-degree agreement on polynomial generators extends to all polynomials
-- statement:
--   Two algebra homomorphisms from a multivariate polynomial ring to a power series ring agree on every polynomial below a strict total-degree cutoff whenever they agree on each generator below that cutoff.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPowerSeries.Equiv

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.coeff_algHom_congr_below_totalDegree
    {σ τ A : Type*} [Fintype τ] [CommSemiring A]
    (F G : MvPolynomial σ A →ₐ[A] MvPowerSeries τ A) (T : ℕ)
    (h : ∀ (i : σ) (d : τ → ℕ), (∑ j, d j) < T →
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
          (F (MvPolynomial.X i)) =
        MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d)
          (G (MvPolynomial.X i)))
    (P : MvPolynomial σ A) (d : τ → ℕ) (hd : (∑ j, d j) < T) :
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (F P) =
      MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm d) (G P) := by sorry
