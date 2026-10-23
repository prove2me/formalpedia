-- Prove2me | Theorems.Thm_HGL_quotient_iso
-- name    : HGL.quotient_iso
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T20:09:32.998919+00:00
-- url     : https://prove2.me/theorems/4c177470-a9fa-4a63-a9a7-1c2ec99d707e
-- title:
--   The class group is the braid group modulo the trivial braids (Theorem 3.7)
-- statement:
--   The class group is isomorphic to the quotient of the surface braid group by the normal subgroup of link-homotopically trivial braids. The composite of the inclusion of the braid group into the monoid of generalized string links with the class map is a homomorphism onto the class group - surjective because every generalized string link is link-homotopic to a braid, by Theorem 3.5 - and its kernel is exactly the subgroup of link-homotopically trivial braids. This identifies the abstract class group with the concrete quotient of Theorem 3.7.
-- source:
--   J. R. T. Theodoro de Lima, Homotopy of braids on surfaces: extending Goldsmith's answer to Artin, Journal of Knot Theory and Its Ramifications 28 (2019) 1950013, arXiv:1811.02006, Section 3 (Theorem 3.7, the isomorphism with the quotient of the surface braid group).

import Mathlib
import Definitions.Def_HGL_alg
import Definitions.Def_HGL_tor

namespace HGL

/-!  Milestone 5 (Theorem 3.7, isomorphism): the group of link-homotopy
classes of generalized string links is isomorphic to the quotient of the
braid group by the normal subgroup of link-homotopically trivial braids.
The inclusion of the braid group followed by the class map is a surjective
homomorphism - by Theorem 3.5 every generalized string link is
link-homotopic to a braid - whose kernel is exactly the subgroup of trivial
braids. -/
theorem quotient_iso {n g : ℕ} {B S Cl : Type*} [Group B] [Monoid S] [Group Cl]
    (W : LinkHomotopyWorld n g B S Cl) :
    ∃ e : B →* Cl, (∀ b : B, e b = W.cls (W.incl b)) ∧
      (∀ c : Cl, ∃ b : B, e b = c) ∧
      (∀ b : B, e b = 1 ↔ EqvGen W.moves (W.incl b) 1) := by sorry

end HGL
