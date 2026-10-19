-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_monic_division_normal_form
-- name    : OAI.PiExponent.LogarithmicJetIdeals.monic_division_normal_form
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T22:32:52.915681+00:00
-- url     : https://prove2.me/theorems/540fb410-edea-405a-afd5-0ca6d9d8c152
-- title:
--   Normal forms by finite monic multivariate division
-- statement:
--   Division by a finite family of monic multivariate polynomials produces a remainder whose supported exponents are divisible by none of their leading monomials, with the difference in the ideal they generate.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Data.Real.Basic

open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.monic_division_normal_form
    {ι : Type*} [Fintype ι] {𝕜 : Type*} [Field 𝕜]
    (o : MonomialOrder ι)
    (S : Finset (MvPolynomial ι 𝕜))
    (P : MvPolynomial ι 𝕜)
    (hmonic : ∀ g ∈ S, o.leadingCoeff g = 1) :
    ∃ Q : MvPolynomial ι 𝕜,
      (∀ u ∈ Q.support, ∀ g ∈ S, ¬ (o.degree g ≤ u)) ∧
      P - Q ∈ Ideal.span (↑S : Set (MvPolynomial ι 𝕜)) := by sorry
