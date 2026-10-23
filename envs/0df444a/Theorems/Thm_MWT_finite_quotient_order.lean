-- Prove2me | Theorems.Thm_MWT_finite_quotient_order
-- name    : MWT.finite_quotient_order
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T20:11:41.914773+00:00
-- url     : https://prove2.me/theorems/5e874383-26bd-4cb8-997b-11f082307a71
-- title:
--   A finite quotient of order at least 2^k n! exists (Theorem 2.7 (iv))
-- statement:
--   The multi-welded twin group admits a finite quotient whose order is at least 2^k n!, which is strictly larger than the order of the symmetric group whenever k is at least one. The quotient is the image of the marked homomorphism into the product of the symmetric group with the elementary Abelian 2-group of rank k+1: the image contains the whole symmetric factor and, for each family, a distinct nontrivial element of the 2-group. This is Theorem 2.7 (iv) of the paper, the main structural lower bound.
-- source:
--   M. N. Nasser, O. Ocampo, Multi-welded twin groups, arXiv:2605.31298 (2026), Section 2 (Theorem 2.7 (iv), the main structural lower bound).

import Mathlib
import Definitions.Def_MWT_alg
import Definitions.Def_MWT_tor

namespace MWT

/-!  The goal (Theorem 2.7 (iv)): the multi-welded twin group M_kWT_n
admits a finite quotient whose order is at least 2^k n!, strictly larger
than the order of the symmetric group for k at least one. The quotient is
the image of the marked homomorphism of Milestone 7 into the product of the
symmetric group with the elementary Abelian 2-group of rank k+1. -/
theorem finite_quotient_order {n k : ℕ} {G UW : Type*} [Group G] [Group UW]
    (W : MultiWeldedTwinWorld n k G UW) :
    ∃ (F : Type) (_ : Group F) (_ : Fintype F) (q : G →* F),
      2 ^ k * Nat.factorial n ≤ Fintype.card F := by sorry

end MWT
