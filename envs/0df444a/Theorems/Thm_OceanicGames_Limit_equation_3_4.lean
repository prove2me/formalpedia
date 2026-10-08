-- Prove2me | Theorems.Thm_OceanicGames_Limit_equation_3_4
-- name    : OceanicGames.Limit.equation_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:43:56.627006+00:00
-- url     : https://prove2.me/theorems/c9412ea2-bb75-44af-a1e1-a987794efbc7
-- title:
--   Equation (3.4) — decompose a major player's value by predecessor coalition
-- statement:
--   Fix a major player $i$. For each set $S$ of other major players, $B_{i,S}$ is the part of the unit cube where precisely the players in $S$ appear before $i$; $A_i$ is the pivotal event. The oceanic value decomposes as
--
--   $$\phi_i=\sum_{S\subseteq M\setminus\{i\}}\mu^m(A_i\cap B_{i,S}).$$
--
--   This partitions the pivotal volume into cells indexed by predecessor coalitions, the first step in comparing the oceanic value with the appendix formula.
--
--   **Formalization Note** The cells use strict precedence for players in $S$ and weak precedence for the others; the value is product Lebesgue volume on the cube.
-- source:
--   Milnor & Shapley, Values of Large Games II: Oceanic Games, RAND RM-2649 (1961), §3 (3.3)–(3.4), p. 8; https://www.rand.org/pubs/research_memoranda/RM2649.html

import Mathlib
import Definitions.Def_OceanicGames_Limit_Basic

namespace OceanicGames.Limit

open MeasureTheory Set Finset

/-- Equation (3.4): split the pivotal region by the predecessor set. -/
theorem equation_3_4 {m : ℕ} (c alpha : ℝ) (w : Fin m → ℝ) (i : Fin m)
    (hc : 0 ≤ c) (halpha : 0 < alpha) (hw : ∀ j, 0 ≤ w j) :
    OceanicGames.Interior.value c alpha w i =
      ∑ S ∈ (Finset.univ.erase i).powerset,
        (volume (OceanicGames.Interior.pivotSet c alpha w i ∩ orderSet i S)).toReal := by sorry

end OceanicGames.Limit
