-- Prove2me | Theorems.Thm_GottschalkSurjunctivity_isSurjunctive_of_isAmenable
-- name    : GottschalkSurjunctivity.isSurjunctive_of_isAmenable
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-30T16:22:05.154854+00:00
-- url     : https://prove2.me/theorems/5c95f54b-43db-4999-a66d-f9d957fa35a9
-- title:
--   Amenable groups are surjunctive
-- statement:
--   **Theorem (Ceccherini-Silberstein, Machì, Scarabotti 1999).** Every amenable group is surjunctive. Here $G$ is amenable if there is a finitely additive probability measure $m$ on all subsets of $G$ that is left-invariant: $m(gE) = m(E)$ for all $g\in G$, $E\subseteq G$.
--
--   The proof in the source goes through the Garden of Eden theorem for amenable groups.
--
--   **Formalization Note** Amenability is the existing platform definition `Garrido.IsAmenable`, with values in $[0,\infty]$.
-- source:
--   T. Ceccherini-Silberstein, A. Machi, F. Scarabotti, Amenable groups and cellular automata, Ann. Inst. Fourier 49 (1999) 673-685, https://doi.org/10.5802/aif.1686

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs
import Definitions.Def_Garrido_Amenability

namespace GottschalkSurjunctivity

theorem isSurjunctive_of_isAmenable (G : Type) [Group G]
    (hG : Garrido.IsAmenable G) : IsSurjunctive G := by sorry

end GottschalkSurjunctivity
