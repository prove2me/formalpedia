-- Prove2me | Theorems.Thm_Garrido_isAmenable_of_isSolvable_of_finiteIndex
-- name    : Garrido.isAmenable_of_isSolvable_of_finiteIndex
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-23T19:34:14.568135+00:00
-- url     : https://prove2.me/theorems/72c6c609-2141-45de-aa31-3a00cb5399aa
-- title:
--   Corollary 2.4 — every virtually solvable group is amenable
-- statement:
--   Let $G$ be a group with a subgroup $H \le G$ of finite index that is solvable.
--   Then $G$ is amenable.
--
--   "Virtually solvable" is spelled out by hypotheses rather than by a named predicate: $H$ carries
--   Mathlib's finite-index typeclass and its solvability is `Group.IsSolvable` on $H$ as a group in
--   its own right. $H$ is **not** assumed normal, and the same $H$ carries both hypotheses.
--
--   Two details that are easy to miss because they sit in instance-implicit position: finite index
--   means the number of **left** cosets $G/H$ is finite, and solvability is solvability of the
--   subtype $H$ with its own group structure, whose derived series starts at $H$ rather than at
--   $G$.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 7, Corollary 2.4; https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_Amenability

namespace Garrido

theorem isAmenable_of_isSolvable_of_finiteIndex {G : Type*} [Group G]
    (H : Subgroup G) [H.FiniteIndex] (hH : Group.IsSolvable H) :
    IsAmenable G := by
  sorry

end Garrido
