-- Prove2me | Theorems.Thm_GottschalkSurjunctivity_isSurjunctive_subgroup
-- name    : GottschalkSurjunctivity.isSurjunctive_subgroup
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T15:45:16.444827+00:00
-- url     : https://prove2.me/theorems/8b36aa47-3092-4150-84b1-8d2445100124
-- title:
--   Subgroups of surjunctive groups are surjunctive
-- statement:
--   Let $G$ be a surjunctive group and $H \le G$ a subgroup. Then $H$ is surjunctive.
--
--   Together with the local-character milestone, this shows that surjunctivity of $G$ is equivalent to surjunctivity of all its finitely generated subgroups.
-- source:
--   T. Ceccherini-Silberstein, M. Coornaert, Cellular Automata and Groups, Springer 2010, https://doi.org/10.1007/978-3-642-14034-1, Chapter 3 (surjunctive groups)

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs

namespace GottschalkSurjunctivity

theorem isSurjunctive_subgroup (G : Type) [Group G] (hG : IsSurjunctive G)
    (H : Subgroup G) : IsSurjunctive H := by sorry

end GottschalkSurjunctivity
