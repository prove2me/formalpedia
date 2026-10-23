-- Prove2me | Theorems.Thm_MWT_symmetric_smallest
-- name    : MWT.symmetric_smallest
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:10:21.377316+00:00
-- url     : https://prove2.me/theorems/88c404b5-b678-4b69-9451-ddffcbd15fec
-- title:
--   The symmetric group is the smallest non-Abelian finite quotient for n at least five (Theorem 2.7 (iii))
-- statement:
--   For n at least five, the symmetric group is the smallest non-Abelian finite quotient of the multi-welded twin group. The permutation epimorphism realizes the symmetric group as a quotient - every permutation is the image of some element - and every finite quotient of order strictly less than n factorial is Abelian. This is Theorem 2.7 (iii) of the paper.
-- source:
--   M. N. Nasser, O. Ocampo, Multi-welded twin groups, arXiv:2605.31298 (2026), Section 2 (Theorem 2.7 (iii)).

import Mathlib
import Definitions.Def_MWT_alg
import Definitions.Def_MWT_tor

namespace MWT

/-!  Milestone 6 (Theorem 2.7 (iii)): for n at least five, the symmetric
group S_n is the smallest non-Abelian finite quotient of the multi-welded
twin group. The permutation map realizes S_n as a quotient, and every
finite quotient of order strictly less than n! is Abelian. -/
theorem symmetric_smallest {n k : ℕ} {G UW : Type*} [Group G] [Group UW]
    (W : MultiWeldedTwinWorld n k G UW) (hn : 5 ≤ n) :
    (∀ p : Equiv.Perm (Fin n), ∃ x : G, W.perm x = p) ∧
    FiniteQuotientsAbelianBelow G (Nat.factorial n) := by sorry

end MWT
