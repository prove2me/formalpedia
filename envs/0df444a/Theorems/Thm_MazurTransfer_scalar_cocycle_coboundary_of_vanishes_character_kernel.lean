-- Prove2me | Theorems.Thm_MazurTransfer_scalar_cocycle_coboundary_of_vanishes_character_kernel
-- name    : MazurTransfer.scalar_cocycle_coboundary_of_vanishes_character_kernel
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-16T06:33:03.1203+00:00
-- url     : https://prove2.me/theorems/99fa9fd0-3cd5-4e91-8011-86c4df855fe2
-- title:
--   A scalar cocycle vanishing on the character kernel is a coboundary
-- statement:
--   Let $k$ be a field, $G$ a group, and $\chi:G\to k^\times$ a character. Suppose $c:G\to k$ satisfies
--
--   $$c(gh)=c(g)+\chi(g)c(h).$$
--
--   If $c$ vanishes on $\ker\chi$, then there exists $a\in k$ such that
--
--   $$c(g)=\chi(g)a-a\qquad(g\in G).$$
--
--   The group and the character image may be infinite.
-- source:
--   Derived scalar-cocycle lemma for the MazurTorsion order-13 descent. Primary cocycle convention: Mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean, groupCohomology.mem_cocycles₁_iff and IsCocycle₁ (https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/RepresentationTheory/Homological/GroupCohomology/LowDegree.lean). The proof uses only the stated scalar cocycle equation, vanishing on the character kernel, and field operations.

import Mathlib

theorem MazurTransfer.scalar_cocycle_coboundary_of_vanishes_character_kernel :
    ∀ (k G : Type) [Field k] [Group G] (χ : G →* kˣ) (c : G → k),
    (∀ g h, c (g * h) = c g + (χ g : k) * c h) →
    (∀ g, χ g = 1 → c g = 0) →
    ∃ a : k, ∀ g, c g = (χ g : k) * a - a := by sorry
