-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_support_sum_eq_column_sum
-- name    : OAI.PiExponent.DeterminantContradiction.weighted_support_sum_eq_column_sum
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-23T07:14:05.341989+00:00
-- url     : https://prove2.me/theorems/33399a33-ca39-4d8e-80a5-6aff3b7a9292
-- title:
--   Reindex a weighted support sum by interpolation columns
-- statement:
--   A function summed over polynomial support has the same sum when indexed by weighted-simplex columns, provided every supported exponent has weight at most `H`. The exponent-vector equivalence reindexes the supported terms; columns whose exponents are outside the support contribute zero. The inclusive `≤ H` condition matches the column definition, including boundary exponents. This handles the only use of `WeightedPolynomial` in the parent.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Classical
open scoped BigOperators
noncomputable section

theorem OAI.PiExponent.DeterminantContradiction.weighted_support_sum_eq_column_sum
    {m : Nat} (w0 : Real) (w : Fin m → Real) (H : Real)
    (P : MvPolynomial (Fin (m + 1)) Complex)
    (f : (Fin (m + 1) →₀ Nat) → Complex)
    (hP : ∀ a ∈ P.support,
      ∑ i, InterpolationMatrix.columnWeights w0 w i * (a i : Real) ≤ H) :
    (∑ a ∈ P.support, f a) =
      ∑ c : InterpolationMatrix.Column w0 w H,
        f (InterpolationMatrix.exponentVector c.1) := by sorry
