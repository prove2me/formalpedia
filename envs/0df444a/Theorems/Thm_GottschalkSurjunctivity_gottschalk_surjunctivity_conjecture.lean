-- Prove2me | Theorems.Thm_GottschalkSurjunctivity_gottschalk_surjunctivity_conjecture
-- name    : GottschalkSurjunctivity.gottschalk_surjunctivity_conjecture
-- status  : Disproved
-- author  : @Lucas
-- created : 2026-09-30T17:08:37.249891+00:00
-- url     : https://prove2.me/theorems/50eb0c03-3637-4ab8-bc6d-10164c47ce09
-- title:
--   Gottschalk's surjunctivity conjecture
-- statement:
--   **Gottschalk's surjunctivity conjecture (1973).** Every group $G$ is surjunctive: for every finite nonempty alphabet $A$ (with the discrete topology), every injective, continuous map $\tau : A^G \to A^G$ commuting with the left shift $(g\cdot x)(h) = x(g^{-1}h)$ is surjective. Equivalently, every injective cellular automaton over $G$ with a finite alphabet is surjective.
--
--   This is an open problem; it is known for sofic groups, a class containing all amenable and all residually finite groups.
--
--   **Formalization Note** $G$ ranges over groups in `Type`; the notion of surjunctivity is `GottschalkSurjunctivity.IsSurjunctive`.
-- source:
--   Formal Conjectures project, file `SurjunctiveGroup.lean` (Gottschalk's surjunctivity conjecture); W. H. Gottschalk, Some general dynamical notions, LNM 318 (1973), pp. 120-125, https://doi.org/10.1007/BFb0061728

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs

namespace GottschalkSurjunctivity

theorem gottschalk_surjunctivity_conjecture (G : Type) [Group G] :
    IsSurjunctive G := by sorry

end GottschalkSurjunctivity
