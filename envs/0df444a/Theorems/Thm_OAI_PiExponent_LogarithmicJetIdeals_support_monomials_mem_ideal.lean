-- Prove2me | Theorems.Thm_OAI_PiExponent_LogarithmicJetIdeals_support_monomials_mem_ideal
-- name    : OAI.PiExponent.LogarithmicJetIdeals.support_monomials_mem_ideal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-14T19:37:55.734356+00:00
-- url     : https://prove2.me/theorems/78034989-1cda-4369-86aa-e4d3052ffabb
-- title:
--   Support monomial membership implies polynomial ideal membership
-- statement:
--   If the coefficient-one monomial at every exponent in a polynomial's support belongs to an ideal, then the polynomial belongs to that ideal.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/AdmissibleMatrixGeometry.lean#L41-L44

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem OAI.PiExponent.LogarithmicJetIdeals.support_monomials_mem_ideal
    {m : ℕ} (I : Ideal (MvPolynomial (Fin (m + 1)) ℂ))
    (Q : MvPolynomial (Fin (m + 1)) ℂ)
    (h : ∀ d ∈ Q.support, MvPolynomial.monomial d (1 : ℂ) ∈ I) :
    Q ∈ I := by
  sorry
