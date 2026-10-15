-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_formalJet_coefficients_surjective_of_kronecker
-- name    : OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficients_surjective_of_kronecker
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T23:04:27.191728+00:00
-- url     : https://prove2.me/theorems/07b9276b-3638-4910-9150-c0eb9447b977
-- title:
--   Surjectivity from a Kronecker family of logarithmic jet coefficients
-- statement:
--   Given a finite family of polynomial witnesses with Kronecker coefficient values, arbitrary assignments to the requested coefficients are realized by a finite linear combination of those witnesses.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Mathlib.RingTheory.Ideal.Operations

open OAI.PiExponent.AdmissibleFormalInterpolation

theorem OAI.PiExponent.LogarithmicJetIdeals.formalJet_coefficients_surjective_of_kronecker
    {ι α : Type} [Fintype α] [DecidableEq α] {m : ℕ}
    (center : ι → Fin m → ℂ) (slot : α → ι)
    (degree : α → Fin (m + 1) → ℕ)
    (hdiag : ∀ a : α,
      ∃ P : MvPolynomial (Fin (m + 1)) ℂ,
        ∀ b : α,
          MvPowerSeries.coeff
            (Finsupp.equivFunOnFinite.symm (degree b))
            (formalJet (center (slot b)) P) = if b = a then 1 else 0) :
    Function.Surjective (fun P : MvPolynomial (Fin (m + 1)) ℂ =>
      fun a : α => MvPowerSeries.coeff
        (Finsupp.equivFunOnFinite.symm (degree a))
        (formalJet (center (slot a)) P)) := by sorry
