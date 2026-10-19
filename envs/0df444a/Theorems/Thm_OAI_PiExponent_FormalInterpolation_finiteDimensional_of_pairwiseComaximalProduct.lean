-- Prove2me | Theorems.Thm_OAI_PiExponent_FormalInterpolation_finiteDimensional_of_pairwiseComaximalProduct
-- name    : OAI.PiExponent.FormalInterpolation.finiteDimensional_of_pairwiseComaximalProduct
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-18T13:24:28.210329+00:00
-- url     : https://prove2.me/theorems/60d4534c-4857-4e99-8200-b9973bef6022
-- title:
--   Finite dimensionality for a product of comaximal finite-colength ideals
-- statement:
--   For a finite family of pairwise comaximal ideals, finite-dimensionality of each quotient implies finite-dimensionality of the quotient by their product, including the empty-family case.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

theorem OAI.PiExponent.FormalInterpolation.finiteDimensional_of_pairwiseComaximalProduct
    {m K : Nat}
    (I : Fin K → Ideal (MvPolynomial (Fin (m + 1)) Complex))
    (hfd : ∀ j, FiniteDimensional Complex
      (MvPolynomial (Fin (m + 1)) Complex ⧸ I j))
    (hcomax : ∀ j₁ j₂ : Fin K, j₁ ≠ j₂ →
      IsCoprime (I j₁) (I j₂)) :
    FiniteDimensional Complex
      (MvPolynomial (Fin (m + 1)) Complex ⧸ ∏ j, I j) := by sorry
