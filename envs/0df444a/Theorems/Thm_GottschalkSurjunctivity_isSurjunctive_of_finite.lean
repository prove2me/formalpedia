-- Prove2me | Theorems.Thm_GottschalkSurjunctivity_isSurjunctive_of_finite
-- name    : GottschalkSurjunctivity.isSurjunctive_of_finite
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T16:07:28.839463+00:00
-- url     : https://prove2.me/theorems/4e167b7f-a6f6-4ae1-9674-57cc05cd811f
-- title:
--   Finite groups are surjunctive
-- statement:
--   Every finite group is surjunctive: if $G$ is finite, then every injective map $A^G\to A^G$ is surjective, because $A^G$ is a finite set.
--
--   This is the base case of the conjecture, stated in the source together with the conjecture.
-- source:
--   Formal Conjectures project, file `SurjunctiveGroup.lean` (Gottschalk's surjunctivity conjecture); W. H. Gottschalk, Some general dynamical notions, LNM 318 (1973), pp. 120-125, https://doi.org/10.1007/BFb0061728 (theorem `isSurjunctive_of_finite`)

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs

namespace GottschalkSurjunctivity

theorem isSurjunctive_of_finite (G : Type) [Group G] [Finite G] :
    IsSurjunctive G := by sorry

end GottschalkSurjunctivity
