-- Prove2me | Theorems.Thm_HHRControl_PV_example_4_17
-- name    : HHRControl.PV.example_4_17
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:36.860131+00:00
-- url     : https://prove2.me/theorems/8bbc3f98-5081-48a7-8409-5728b5e0823e
-- title:
--   Example 4.17, p. 15 — approval voting is susceptible to constructive control by partition of voters in models TE and TP
-- statement:
--   **Example 4.17.** Let $C=\{a,b,c\}$ and let $V$ consist of eight approval voters (bits for $a,b,c$):
--   $$v_1=v_2=v_3=100,\quad v_4=v_5=010,\quad v_6=v_7=v_8=001.$$
--   In $(C,V)$, $a$ and $c$ are tied. For $V_1=\{v_1,v_2,v_6,v_7,v_8\}$ and $V_2=\{v_3,v_4,v_5\}$, $c$ is the unique approval winner of $(C,V_1)$, $b$ of $(C,V_2)$, and $c$ wins the run-off against $b$, in model TE and in model TP. Consequently approval voting is susceptible to constructive control by partition of voters in both models.
--
--   This election witnesses the susceptibility part of the approval constructive clauses of Theorem 3.6.
--
--   Differences from the source:
--   - encoding: candidates a, b, c; voters v1, v2, … → candidates 0, 1, 2 of Fin 3; voter vᵢ is index i − 1 of Fin n; reason: 0-based indices; no instance changes
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, arXiv:cs/0507027v5, p. 15, Example 4.17

import Mathlib
import Definitions.Def_HHRControl_PV_Elections

namespace HHRControl.PV

open Finset

/-- Example 4.17, p. 15: approval voting is susceptible to constructive control by partition of
voters, in models TE and TP. Candidates `a, b, c` are `0, 1, 2`; an approval ballot is the set of
approved candidates. -/
theorem example_4_17 :
    (let P : Fin 8 → Approval 3 := ![{0}, {0}, {0}, {1}, {1}, {2}, {2}, {2}];
      approval.winners 3 8 P univ univ = {0, 2} ∧
      approval.winners 3 8 P univ {0, 1, 5, 6, 7} = {2} ∧
      approval.winners 3 8 P univ ({0, 1, 5, 6, 7} : Finset (Fin 8))ᶜ = {1} ∧
      ∀ rule : TieRule, twoStage rule approval P {0, 1, 5, 6, 7} = {2}) ∧
    SusceptibleCC .TE approval ∧ SusceptibleCC .TP approval := by sorry

end HHRControl.PV
