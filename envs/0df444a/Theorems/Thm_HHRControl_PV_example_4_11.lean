-- Prove2me | Theorems.Thm_HHRControl_PV_example_4_11
-- name    : HHRControl.PV.example_4_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:37.95771+00:00
-- url     : https://prove2.me/theorems/5882cefb-ff71-4ec5-ab1b-4809bc2684d7
-- title:
--   Example 4.11, p. 13 — approval voting is susceptible to destructive control by partition of voters in models TE and TP
-- statement:
--   **Example 4.11.** Let $C=\{a,b,c\}$ and let $V$ consist of ten approval voters (bits for $a,b,c$):
--   $$v_1=v_2=v_3=v_4=001,\quad v_5=v_6=v_7=100,\quad v_8=v_9=v_{10}=010.$$
--   Then $c$ is the unique approval winner of $(C,V)$. For $V_1=\{v_1,v_2,v_5,v_6,v_7\}$ and $V_2=V-V_1$, $a$ is the unique winner of $(C,V_1)$ and $b$ of $(C,V_2)$; they are nominated and tie in the final election, in model TE and in model TP. Consequently approval voting is susceptible to destructive control by partition of voters in both models.
--
--   This election witnesses the susceptibility part of the approval destructive clauses of Theorem 3.6.
--
--   Differences from the source:
--   - encoding: candidates a, b, c; voters v1, v2, … → candidates 0, 1, 2 of Fin 3; voter vᵢ is index i − 1 of Fin n; reason: 0-based indices; no instance changes
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, arXiv:cs/0507027v5, p. 13, Example 4.11

import Mathlib
import Definitions.Def_HHRControl_PV_Elections

namespace HHRControl.PV

open Finset

/-- Example 4.11, p. 13: approval voting is susceptible to destructive control by partition of
voters, in models TE and TP. Candidates `a, b, c` are `0, 1, 2`; an approval ballot is the set of
approved candidates. -/
theorem example_4_11 :
    (let P : Fin 10 → Approval 3 :=
        ![{2}, {2}, {2}, {2}, {0}, {0}, {0}, {1}, {1}, {1}];
      approval.winners 3 10 P univ univ = {2} ∧
      approval.winners 3 10 P univ {0, 1, 4, 5, 6} = {0} ∧
      approval.winners 3 10 P univ ({0, 1, 4, 5, 6} : Finset (Fin 10))ᶜ = {1} ∧
      ∀ rule : TieRule, twoStage rule approval P {0, 1, 4, 5, 6} = {0, 1}) ∧
    SusceptibleDC .TE approval ∧ SusceptibleDC .TP approval := by sorry

end HHRControl.PV
