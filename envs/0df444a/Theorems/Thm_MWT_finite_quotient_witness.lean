-- Prove2me | Theorems.Thm_MWT_finite_quotient_witness
-- name    : MWT.finite_quotient_witness
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-10-22T20:11:04.984653+00:00
-- url     : https://prove2.me/theorems/a10b30c0-84a4-49d9-8393-7799a95d6a10
-- title:
--   A marked finite quotient of order at least 2^k n! (Theorem 2.7 (iv), construction)
-- statement:
--   The multi-welded twin group admits a marked finite quotient of order at least 2^k n!: a homomorphism to the product of the symmetric group with an elementary Abelian 2-group A of order 2^(k+1), whose first component is the permutation map, and whose second component separates the twin generator from each virtual generator - the image of the product of the twin generator and the virtual generator of any family is a nontrivial element of A. This is the witnessing construction of Theorem 2.7 (iv) of the paper.
-- source:
--   M. N. Nasser, O. Ocampo, Multi-welded twin groups, arXiv:2605.31298 (2026), Section 2 (Theorem 2.7 (iv), the witnessing construction).

import Mathlib
import Definitions.Def_MWT_alg
import Definitions.Def_MWT_tor

namespace MWT

/-!  Milestone 7 (Theorem 2.7 (iv), construction): the multi-welded twin
group admits a marked finite quotient of order at least 2^k n!: a
homomorphism to the product of the symmetric group with an elementary
Abelian 2-group A of order 2^(k+1), whose first component is the
permutation map, and whose second component separates the twin generator
from each virtual generator - the images of s_i and rho_i^(alpha) differ
in A. -/
theorem finite_quotient_witness {n k : ℕ} {G UW : Type*} [Group G] [Group UW]
    (W : MultiWeldedTwinWorld n k G UW) :
    ∃ (A : Type) (_ : CommGroup A) (_ : Fintype A) (hA : Fintype.card A = 2 ^ (k + 1))
      (th : G →* Equiv.Perm (Fin n) × A),
      (∀ x : G, (th x).1 = W.perm x) ∧
      (∀ (i : Fin (n - 1)) (α : Fin k), (th (W.s i * W.rho α i)).2 ≠ 1) := by sorry

end MWT
