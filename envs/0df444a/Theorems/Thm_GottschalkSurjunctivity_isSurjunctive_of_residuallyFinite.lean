-- Prove2me | Theorems.Thm_GottschalkSurjunctivity_isSurjunctive_of_residuallyFinite
-- name    : GottschalkSurjunctivity.isSurjunctive_of_residuallyFinite
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T16:13:06.603261+00:00
-- url     : https://prove2.me/theorems/b692986a-2322-4460-8016-d91e771d8c81
-- title:
--   Residually finite groups are surjunctive (Lawton)
-- statement:
--   **Theorem (Lawton; reported by Gottschalk, 1973).** Every residually finite group is surjunctive. Here $G$ is residually finite if for every $g \neq 1$ there is a normal subgroup $N \trianglelefteq G$ of finite index with $g \notin N$.
--
--   This covers, for example, all finitely generated linear groups and all free groups.
-- source:
--   Formal Conjectures project, file `SurjunctiveGroup.lean` (Gottschalk's surjunctivity conjecture); W. H. Gottschalk, Some general dynamical notions, LNM 318 (1973), pp. 120-125, https://doi.org/10.1007/BFb0061728; T. Ceccherini-Silberstein, M. Coornaert, Cellular Automata and Groups, Springer 2010, https://doi.org/10.1007/978-3-642-14034-1, Chapter 3

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs

namespace GottschalkSurjunctivity

theorem isSurjunctive_of_residuallyFinite (G : Type) [Group G]
    (hG : IsResiduallyFinite G) : IsSurjunctive G := by sorry

end GottschalkSurjunctivity
