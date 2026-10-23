-- Prove2me | Theorems.Thm_HGL_trivial_braids_normal
-- name    : HGL.trivial_braids_normal
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T20:08:22.492248+00:00
-- url     : https://prove2.me/theorems/c0dc04b3-7b2d-425c-946c-79a54c3bc48c
-- title:
--   The group of link-homotopically trivial braids is normal (Proposition 3.6)
-- statement:
--   Every subgroup of the surface braid group whose membership is link-homotopical triviality is normal: the conjugate of a link-homotopically trivial braid by any braid is again link-homotopically trivial. The group of trivial braids of Proposition 3.6 is therefore a normal subgroup of the surface braid group, and the quotient by it is a group.
-- source:
--   J. R. T. Theodoro de Lima, Homotopy of braids on surfaces: extending Goldsmith's answer to Artin, Journal of Knot Theory and Its Ramifications 28 (2019) 1950013, arXiv:1811.02006, Section 3 (Proposition 3.6, the normality assertion).

import Mathlib
import Definitions.Def_HGL_alg
import Definitions.Def_HGL_tor

namespace HGL

/-!  Milestone 3 (Proposition 3.6): the group H_n(M) of link-homotopically
trivial surface braids is a normal subgroup of the surface braid group
B_n(M). Any subgroup of the braid group whose membership is the triviality
under link homotopy is normal: conjugation of a trivial braid by a braid
remains trivial, because the class map is compatible with the braid group
multiplication. -/
theorem trivial_braids_normal {n g : ℕ} {B S Cl : Type*} [Group B] [Monoid S] [Group Cl]
    (W : LinkHomotopyWorld n g B S Cl) :
    ∀ H : Subgroup B, (∀ b : B, b ∈ H ↔ EqvGen W.moves (W.incl b) 1) → H.Normal := by sorry

end HGL
