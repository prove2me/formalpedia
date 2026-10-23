-- Prove2me | Theorems.Thm_MWT_commutator_perfect
-- name    : MWT.commutator_perfect
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:09:45.361527+00:00
-- url     : https://prove2.me/theorems/0734bd47-61cd-4567-b98c-9d7925a21d1a
-- title:
--   The commutator subgroup is perfect for n at least five (Theorem 2.7 (ii))
-- statement:
--   For n at least five, the commutator subgroup of the multi-welded twin group is perfect: the derived subgroup of the derived subgroup is the whole derived subgroup. The rigidity of the universal welded framework descends to the involutive quotient, and every commutator of two elements of the commutator subgroup is again a product of commutators of elements of the commutator subgroup. This is Theorem 2.7 (ii) of the paper.
-- source:
--   M. N. Nasser, O. Ocampo, Multi-welded twin groups, arXiv:2605.31298 (2026), Section 2 (Theorem 2.7 (ii)).

import Mathlib
import Definitions.Def_MWT_alg
import Definitions.Def_MWT_tor

namespace MWT

/-!  Milestone 5 (Theorem 2.7 (ii)): for n at least five, the commutator
subgroup of the multi-welded twin group is perfect - the derived subgroup
of the derived subgroup is everything. The rigidity of the universal
welded framework descends to the involutive quotient. -/
theorem commutator_perfect {n k : ℕ} {G UW : Type*} [Group G] [Group UW]
    (W : MultiWeldedTwinWorld n k G UW) (hn : 5 ≤ n) :
    DerivedPerfect G := by sorry

end MWT
