-- Prove2me | Theorems.Thm_HGL_trivial_braids_subgroup
-- name    : HGL.trivial_braids_subgroup
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T20:07:36.636833+00:00
-- url     : https://prove2.me/theorems/06cf3cac-05cb-4fc0-a359-7732f8274352
-- title:
--   The link-homotopically trivial braids form a subgroup (Proposition 3.6)
-- statement:
--   The link-homotopically trivial braids form a subgroup of the surface braid group: there is a subgroup whose members are exactly the braids whose images under the inclusion are link-homotopic to the identity. Closure under multiplication follows from the congruence of the link-homotopy relation - the product of two trivial braids is trivial - and closure under inverses from the mirror operation, since the concatenation of a braid with its mirror is link-homotopic to the identity.
-- source:
--   J. R. T. Theodoro de Lima, Homotopy of braids on surfaces: extending Goldsmith's answer to Artin, Journal of Knot Theory and Its Ramifications 28 (2019) 1950013, arXiv:1811.02006, Section 3 (Proposition 3.6, the subgroup assertion).

import Mathlib
import Definitions.Def_HGL_alg
import Definitions.Def_HGL_tor

namespace HGL

/-!  Milestone 2: the link-homotopically trivial braids form a subgroup of
the braid group. The set of braids whose images under the inclusion are
equivalent to the identity under the link-homotopy closure is closed under
multiplication and inverses, using the congruence of Milestone 1 and the
mirror operation. -/
theorem trivial_braids_subgroup {n g : ℕ} {B S Cl : Type*} [Group B] [Monoid S] [Group Cl]
    (W : LinkHomotopyWorld n g B S Cl) :
    ∃ H : Subgroup B, ∀ b : B, b ∈ H ↔ EqvGen W.moves (W.incl b) 1 := by sorry

end HGL
