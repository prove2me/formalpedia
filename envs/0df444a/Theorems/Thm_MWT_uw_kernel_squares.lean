-- Prove2me | Theorems.Thm_MWT_uw_kernel_squares
-- name    : MWT.uw_kernel_squares
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T20:08:06.552212+00:00
-- url     : https://prove2.me/theorems/f25255a3-7f36-4f22-9bd0-4ef976d8f787
-- title:
--   The kernel of the universal welded epimorphism contains the generator squares (Proposition 2.3)
-- statement:
--   The canonical epimorphism from the universal welded braid group onto the multi-welded twin group kills the squares of all the generators: the squares of the non-virtual generators and the squares of the virtual generators all map to the identity, because every image - the twin generators and the virtual generators of every family - is an involution in the multi-welded twin group. The kernel of the epimorphism of Proposition 2.3 therefore contains the squares of all the generators, and the multi-welded twin group arises as the quotient by an involutivity imposition.
-- source:
--   M. N. Nasser, O. Ocampo, Multi-welded twin groups, arXiv:2605.31298 (2026), Section 2 (Proposition 2.3, the kernel content).

import Mathlib
import Definitions.Def_MWT_alg
import Definitions.Def_MWT_tor

namespace MWT

/-!  Milestone 2 (Proposition 2.3): the canonical epimorphism from the
universal welded braid group UW_n(k) onto the multi-welded twin group
identifies the virtual generators with the distinguished virtual family,
the first k-1 non-virtual families with the remaining virtual families,
and the last non-virtual family with the twin generators; since all
images are involutions, the kernel contains the squares of all non-virtual
generators and of the virtual generators. -/
theorem uw_kernel_squares {n k : ℕ} {G UW : Type*} [Group G] [Group UW]
    (W : MultiWeldedTwinWorld n k G UW) :
    ∀ (i : Fin (n - 1)) (t : Fin k),
      W.uw (W.uwSigma i t * W.uwSigma i t) = 1 ∧
      W.uw (W.uwRho i * W.uwRho i) = 1 := by sorry

end MWT
