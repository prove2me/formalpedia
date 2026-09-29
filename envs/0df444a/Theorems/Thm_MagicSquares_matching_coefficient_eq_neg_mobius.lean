-- Prove2me | Theorems.Thm_MagicSquares_matching_coefficient_eq_neg_mobius
-- name    : MagicSquares.matching_coefficient_eq_neg_mobius
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-23T01:32:53.036997+00:00
-- url     : https://prove2.me/theorems/2436e4cb-003b-423c-bd3a-318933165075
-- title:
--   Matching coefficient equals a support-poset Möbius number
-- statement:
--   Let n be positive and let B be a matching-covered bipartite board. The finite alternating matching coefficient a(B) is the negative Möbius function from the empty board to B in the finite poset consisting of the empty board and all matching-covered boards, ordered by inclusion.
-- source:
--   A self-contained finite Möbius inversion argument for matching-covered boards. It uses the defining principal-ideal prefix identity of the public coefficient and uniqueness of Möbius weights. The matching-covered support poset is related to the Birkhoff-polytope face lattice in Beniamini and Nisan, Bipartite Perfect Matching as a Real Polynomial, arXiv:2001.07642v2, Section 3.2.2, Theorem 3.11; this coefficient identity is proved directly here and is not quoted verbatim from that source. https://arxiv.org/pdf/2001.07642v2

import Mathlib
import Definitions.Def_MagicSquaresMatchingBoundary
attribute [local instance] Classical.propDecidable

namespace MagicSquares

theorem matching_coefficient_eq_neg_mobius (n : ℕ) (hn : 1 ≤ n)
    (B : Finset (Fin n × Fin n))
    (hB : MagicSquaresBoundary.MatchingCoveredBoard n B) :
    MagicSquaresBoundary.matchingEulerCoefficient n B =
      -IncidenceAlgebra.mu ℚ
        (⟨∅, Or.inl rfl⟩ :
          {C : Finset (Fin n × Fin n) //
            C = ∅ ∨ MagicSquaresBoundary.MatchingCoveredBoard n C})
        ⟨B, Or.inr hB⟩ := by
  sorry

end MagicSquares
