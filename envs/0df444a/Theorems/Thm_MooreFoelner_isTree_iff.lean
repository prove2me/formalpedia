-- Prove2me | Theorems.Thm_MooreFoelner_isTree_iff
-- name    : MooreFoelner.isTree_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-01T23:08:03.789587+00:00
-- url     : https://prove2.me/theorems/aca7fef5-082a-4f1b-ac03-35623076fb2b
-- title:
--   §2 — trees are the finite non-empty prefix-free sets in which u⁀0 has an extension exactly when u⁀1 does
-- statement:
--   A finite set $T$ of finite binary sequences is a tree (every infinite sequence has exactly one element of $T$ as an initial part) if and only if $T$ is non-empty, no element of $T$ is an initial part of another, and for every finite sequence $u$ (the empty one included), $u^\frown 0$ has an extension in $T$ exactly when $u^\frown 1$ does, where an extension of $w$ is a sequence having $w$ as an initial part, $w$ itself included.
--
--   **Formalization Note.** Moore's characterization omits non-emptiness; the empty set satisfies both of Moore's conditions but is not a tree, so non-emptiness is added.
-- source:
--   Moore, J. T., Fast growth in the Følner function for Thompson's group F, Groups Geom. Dyn. 7 (2013) 633–651, https://doi.org/10.4171/GGD/201 (arXiv:0905.1118v7, whose page numbers are used), p. 3, §2

import Mathlib
import Definitions.Def_MooreTrees

namespace MooreFoelner

theorem isTree_iff (T : Finset Seq) :
    IsTree T ↔ T.Nonempty ∧ (∀ u ∈ T, ∀ v ∈ T, u <+: v → u = v) ∧
      ∀ u : Seq, (∃ t ∈ T, (u ++ [false]) <+: t) ↔ (∃ t ∈ T, (u ++ [true]) <+: t) := by
  sorry

end MooreFoelner
