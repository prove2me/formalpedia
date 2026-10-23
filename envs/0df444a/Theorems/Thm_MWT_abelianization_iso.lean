-- Prove2me | Theorems.Thm_MWT_abelianization_iso
-- name    : MWT.abelianization_iso
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:09:22.782979+00:00
-- url     : https://prove2.me/theorems/494ae4c6-5f97-440b-aae0-77226d694eb4
-- title:
--   The abelianization is the elementary Abelian 2-group of rank k+1 (Theorem 2.7 (i))
-- statement:
--   The abelianization of the multi-welded twin group is the elementary Abelian 2-group of rank k+1. The k+1 collapsed classes - the class of the twin generators and the classes of the k virtual families - are each of exponent two, by the involutivity of the generators, and they form a basis: the abelianization is multiplicatively equivalent to the group of (k+1)-tuples of bits under pointwise addition. This is Theorem 2.7 (i) of the paper.
-- source:
--   M. N. Nasser, O. Ocampo, Multi-welded twin groups, arXiv:2605.31298 (2026), Section 2 (Theorem 2.7 (i)).

import Mathlib
import Definitions.Def_MWT_alg
import Definitions.Def_MWT_tor

namespace MWT

/-!  Milestone 4 (Theorem 2.7 (i)): the abelianization of the multi-welded
twin group M_kWT_n is the elementary Abelian 2-group of rank k+1: the
classes of the collapsed families, each of exponent two, form a basis. -/
theorem abelianization_iso {n k : ℕ} {G UW : Type*} [Group G] [Group UW]
    (W : MultiWeldedTwinWorld n k G UW) :
    Nonempty (Abelianization G ≃* Multiplicative (Fin (k + 1) → ZMod 2)) := by sorry

end MWT
