-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_finite_coefficients_surjective
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_finite_coefficients_surjective
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-15T05:16:35.804823+00:00
-- url     : https://prove2.me/theorems/b68ab187-b1fb-4f72-a4a2-f61fb13c2ee2
-- title:
--   Finite coefficient interpolation at one formal logarithmic center
-- statement:
--   At one center, arbitrary values can be realized at any finite family of distinct multi-indices as coefficients of the formal logarithmic jet of a polynomial.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_finite_coefficients_surjective
    {α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (center : Fin m → ℂ) (degree : α → Fin (m + 1) → ℕ)
    (hdegree : Function.Injective degree) (value : α → ℂ) :
    ∃ Q : MvPolynomial (Fin (m + 1)) ℂ,
      ∀ b : α,
        MvPowerSeries.coeff
          (Finsupp.equivFunOnFinite.symm (degree b))
          (formalJet center Q) = value b := by sorry
