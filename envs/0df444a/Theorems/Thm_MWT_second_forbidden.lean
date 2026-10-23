-- Prove2me | Theorems.Thm_MWT_second_forbidden
-- name    : MWT.second_forbidden
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T20:07:24.226187+00:00
-- url     : https://prove2.me/theorems/7a452b13-f4bf-4086-a778-7d1a81821e9f
-- title:
--   The two twin-welded forbidden relations are equivalent (Remark 2.2 (2))
-- statement:
--   In the multi-welded twin group, the two twin-welded forbidden relations are equivalent: the product of the two adjacent twin generators with the virtual generator of any family in the first position equals the product with the virtual generator in the last position. The equivalence follows by taking inverses in the welded relation and using that all the generators are involutions: each factor is its own inverse. This is the observation of Remark 2.2 (2) of the paper, which shows that the presentation of Definition 2.1 admits the second forbidden relation as a derived relation.
-- source:
--   M. N. Nasser, O. Ocampo, Multi-welded twin groups, arXiv:2605.31298 (2026), Section 2 (Remark 2.2 (2)).

import Mathlib
import Definitions.Def_MWT_alg
import Definitions.Def_MWT_tor

namespace MWT

/-!  Milestone 1 (Remark 2.2 (2)): the two twin-welded forbidden relations
are equivalent in the multi-welded twin group. Taking inverses in the
welded relation (2.9) and using that all generators are involutions yields
the second forbidden relation s_i s_(i+1) rho_i^(alpha) =
rho_(i+1)^(alpha) s_i s_(i+1). -/
theorem second_forbidden {n k : ℕ} {G UW : Type*} [Group G] [Group UW]
    (W : MultiWeldedTwinWorld n k G UW) (α : Fin k) (i : ℕ) (hi : i + 3 ≤ n) :
    W.s ⟨i, by omega⟩ * W.s ⟨i + 1, by omega⟩ * W.rho α ⟨i, by omega⟩
      = W.rho α ⟨i + 1, by omega⟩ * W.s ⟨i, by omega⟩ * W.s ⟨i + 1, by omega⟩ := by sorry

end MWT
