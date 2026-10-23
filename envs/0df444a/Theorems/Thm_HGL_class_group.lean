-- Prove2me | Theorems.Thm_HGL_class_group
-- name    : HGL.class_group
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T20:08:56.200176+00:00
-- url     : https://prove2.me/theorems/cb392aad-a459-4e33-9a72-9674fbdbb62c
-- title:
--   The link-homotopy classes of generalized string links form a group (Theorem 3.7)
-- statement:
--   The link-homotopy classes of generalized string links form a group under concatenation. Every class contains a generalized string link, and the class of the mirror of any representative is the group inverse of its class: the class of the concatenation of a link with its mirror is the identity. This is the group structure of the class group of Theorem 3.7, the group denoted B-hat of the paper.
-- source:
--   J. R. T. Theodoro de Lima, Homotopy of braids on surfaces: extending Goldsmith's answer to Artin, Journal of Knot Theory and Its Ramifications 28 (2019) 1950013, arXiv:1811.02006, Section 3 (Theorem 3.7, the group structure).

import Mathlib
import Definitions.Def_HGL_alg
import Definitions.Def_HGL_tor

namespace HGL

/-!  Milestone 4 (Theorem 3.7, group structure): the link-homotopy classes
of generalized string links form a group under concatenation. Every class
is represented by a generalized string link, and the class of its mirror
is the group inverse of its class: the mirror of the concatenation with
itself is link-homotopic to the identity. -/
theorem class_group {n g : ℕ} {B S Cl : Type*} [Group B] [Monoid S] [Group Cl]
    (W : LinkHomotopyWorld n g B S Cl) :
    ∀ c : Cl, ∃ s : S, W.cls s = c ∧ c⁻¹ = W.cls (W.mirror s) := by sorry

end HGL
