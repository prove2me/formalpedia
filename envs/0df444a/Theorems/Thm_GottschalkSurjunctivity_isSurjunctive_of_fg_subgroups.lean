-- Prove2me | Theorems.Thm_GottschalkSurjunctivity_isSurjunctive_of_fg_subgroups
-- name    : GottschalkSurjunctivity.isSurjunctive_of_fg_subgroups
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T15:59:15.426605+00:00
-- url     : https://prove2.me/theorems/1290e1b0-de40-46d4-be96-b025d51c5199
-- title:
--   Surjunctivity is a local property
-- statement:
--   Let $G$ be a group such that every finitely generated subgroup $H \le G$ is surjunctive. Then $G$ is surjunctive.
--
--   This reduces the conjecture to finitely generated groups.
-- source:
--   T. Ceccherini-Silberstein, M. Coornaert, Cellular Automata and Groups, Springer 2010, https://doi.org/10.1007/978-3-642-14034-1, Chapter 3 (surjunctive groups)

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs

namespace GottschalkSurjunctivity

theorem isSurjunctive_of_fg_subgroups (G : Type) [Group G]
    (h : ∀ H : Subgroup G, H.FG → IsSurjunctive H) : IsSurjunctive G := by sorry

end GottschalkSurjunctivity
