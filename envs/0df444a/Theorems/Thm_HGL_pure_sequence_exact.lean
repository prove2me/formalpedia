-- Prove2me | Theorems.Thm_HGL_pure_sequence_exact
-- name    : HGL.pure_sequence_exact
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-22T20:09:57.659781+00:00
-- url     : https://prove2.me/theorems/4a9fb39f-7881-4a88-bea3-64ebdae4ab31
-- title:
--   The short exact sequence of the pure link-homotopy classes (Proposition 3.8)
-- statement:
--   The permutation map of the class group onto the symmetric group is surjective, and its kernel is exactly the set of classes of pure braids: a class is pure - represented by a braid with trivial permutation - exactly when it lies in the kernel. The sequence from the pure link-homotopy classes through the class group onto the symmetric group is therefore short exact, the sequence of Proposition 3.8.
-- source:
--   J. R. T. Theodoro de Lima, Homotopy of braids on surfaces: extending Goldsmith's answer to Artin, Journal of Knot Theory and Its Ramifications 28 (2019) 1950013, arXiv:1811.02006, Section 3 (Proposition 3.8).

import Mathlib
import Definitions.Def_HGL_alg
import Definitions.Def_HGL_tor

namespace HGL

/-!  Milestone 6 (Proposition 3.8): the short exact sequence from the pure
link-homotopy classes to the full class group and onto the symmetric
group. The permutation map of the class group is surjective - every
permutation is realized by a braid - and its kernel is exactly the set of
classes of pure braids, so the sequence of Proposition 3.8 is exact. -/
theorem pure_sequence_exact {n g : ℕ} {B S Cl : Type*} [Group B] [Monoid S] [Group Cl]
    (W : LinkHomotopyWorld n g B S Cl) :
    (∀ p : Equiv.Perm (Fin n), ∃ c : Cl, W.permCl c = p) ∧
    (∀ c : Cl, W.permCl c = 1 ↔ ∃ b : B, W.perm b = 1 ∧ W.cls (W.incl b) = c) := by sorry

end HGL
