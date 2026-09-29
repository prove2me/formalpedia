-- Prove2me | Theorems.Thm_MagicSquares_real_cone_face_support_order_iso
-- name    : MagicSquares.real_cone_face_support_order_iso
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-22T15:33:36.991704+00:00
-- url     : https://prove2.me/theorems/db8ce110-88d2-4a2d-982d-6a9731e337bb
-- title:
--   Faces of the real semi-magic cone correspond to matching-covered supports
-- statement:
--   For n at least 1, consider the cone of nonnegative real n by n matrices whose row sums and column sums share one common value. Its faces, ordered by inclusion, are order-isomorphic to the empty board together with matching-covered boards, ordered by cell inclusion. The isomorphism sends a face to the cells that are nonzero in at least one matrix of the face.
-- source:
--   This is an original conic specialization proved from coordinate faces and Birkhoff-von Neumann decomposition. The related polytope statement, that the face lattice of the Birkhoff polytope corresponds to matching-covered graphs plus the empty graph, is Theorem 3.11 in Beniamini and Nisan, Bipartite Perfect Matching as a Real Polynomial, arXiv:2001.07642v2, Section 3.2.2, attributed there to Billera and Sarangarajan. Our real cone and support-witness formulation is not the same sentence. https://arxiv.org/pdf/2001.07642v2

import Mathlib
import Definitions.Def_MagicSquaresRealCone
import Definitions.Def_MagicSquaresMatchingBoundary

namespace MagicSquares

theorem real_cone_face_support_order_iso (n : ℕ) (hn : 1 ≤ n) :
    ∃ e :
      {F : PointedCone ℝ ((Fin n × Fin n) → ℝ) //
        F.IsFaceOf (MagicSquaresRealCone.cone n)} ≃o
      {B : Finset (Fin n × Fin n) //
        B = ∅ ∨ MagicSquaresBoundary.MatchingCoveredBoard n B},
      ∀ F i, i ∈ (e F).val ↔ ∃ x ∈ F.val, x i ≠ 0 := by
  sorry

end MagicSquares
