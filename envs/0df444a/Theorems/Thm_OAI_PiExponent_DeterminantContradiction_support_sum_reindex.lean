-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_support_sum_reindex
-- name    : OAI.PiExponent.DeterminantContradiction.support_sum_reindex
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-23T08:31:40.854106+00:00
-- url     : https://prove2.me/theorems/be7ca616-a4bc-42e0-a3c2-ec1d8a14dbad
-- title:
--   Reindex a polynomial support sum by finite functions
-- statement:
--   Reindex the finite support of a multivariate polynomial by its equivalent finite-function representation, expressing each encoded index through `exponentVector`.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem OAI.PiExponent.DeterminantContradiction.support_sum_reindex
    (m : Nat) (P : MvPolynomial (Fin m) Complex)
    (f : (Fin m →₀ Nat) → Complex) :
    (∑ a ∈ P.support, f a * P.coeff a) =
      ∑ a ∈ P.support.map Finsupp.equivFunOnFinite.toEmbedding,
        f (InterpolationMatrix.exponentVector a) *
          P.coeff (InterpolationMatrix.exponentVector a) := by sorry
