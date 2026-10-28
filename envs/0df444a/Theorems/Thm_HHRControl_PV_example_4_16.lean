-- Prove2me | Theorems.Thm_HHRControl_PV_example_4_16
-- name    : HHRControl.PV.example_4_16
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:47.142417+00:00
-- url     : https://prove2.me/theorems/7ae3eabb-0d6a-4915-a375-69d33b053598
-- title:
--   Example 4.16, p. 14 — plurality is susceptible to constructive and destructive control by partition of voters in model TP
-- statement:
--   **Example 4.16.** Let $C=\{a,b,c\}$ and let $V$ consist of eight voters: $u_1,u_2,u_3$ voting $a>c>b$, $v_1,v_2$ voting $b>a>c$, and $w_1,w_2,w_3$ voting $c>a>b$.
--
--   *Constructive case.* $a$ and $c$ tie for first place in $(C,V)$, so $c$ is not the unique plurality winner. For $V_1=\{u_1,u_2,w_1,w_2,w_3\}$ and $V_2=\{u_3,v_1,v_2\}$, $c$ is the unique winner of $(C,V_1)$, $b$ of $(C,V_2)$, and $c$ wins the run-off against $b$.
--
--   *Destructive case.* Let $V'=V\cup\{v_3,w_4\}$ with $v_3: b>a>c$ and $w_4: c>a>b$. Then $c$ is the unique plurality winner of $(C,V')$. For $V'_1=\{u_1,u_2,u_3,w_1,w_2\}$ and $V'_2=\{v_1,v_2,v_3,w_3,w_4\}$, $a$ is the unique winner of $(C,V'_1)$, $b$ of $(C,V'_2)$, and $a$ wins the run-off against $b$.
--
--   Consequently plurality voting is susceptible to constructive and to destructive control by partition of voters in model TP.
--
--   These elections witness the susceptibility part of the plurality TP clauses of Theorem 3.6.
--
--   Differences from the source:
--   - encoding: candidates a, b, c; voters u1, u2, u3, v1, v2, w1, w2, w3 (then v3, w4) → candidates 0, 1, 2 of Fin 3; the voters are indices 0–7 in that order (then 8, 9); reason: 0-based indices; no instance changes
--   - encoding: voters with the listed preference orders → every profile P whose ballots have the listed codes (rankingCode lists the candidates from most to least preferred); reason: rankingCode is injective, so this is exactly the listed profile; the profile exists
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, arXiv:cs/0507027v5, p. 14, Example 4.16

import Mathlib
import Definitions.Def_HHRControl_PV_Elections

namespace HHRControl.PV

open Finset

/-- Example 4.16, p. 14: plurality voting is susceptible to constructive and to destructive control
by partition of voters in model TP. Candidates `a, b, c` are `0, 1, 2`; a ballot is given by its
code, the candidates from the most to the least preferred. The voters are listed in the order
`u₁, u₂, u₃, v₁, v₂, w₁, w₂, w₃` (then `v₃, w₄` for the election `(C, V′)`). -/
theorem example_4_16 :
    (∀ P : Fin 8 → Ranking 3,
      (∀ v, rankingCode (P v) = ![[0, 2, 1], [0, 2, 1], [0, 2, 1], [1, 0, 2], [1, 0, 2],
          [2, 0, 1], [2, 0, 1], [2, 0, 1]] v) →
        plurality.winners 3 8 P univ univ = {0, 2} ∧
        plurality.winners 3 8 P univ {0, 1, 5, 6, 7} = {2} ∧
        plurality.winners 3 8 P univ ({0, 1, 5, 6, 7} : Finset (Fin 8))ᶜ = {1} ∧
        twoStage .TP plurality P {0, 1, 5, 6, 7} = {2}) ∧
    (∀ P' : Fin 10 → Ranking 3,
      (∀ v, rankingCode (P' v) = ![[0, 2, 1], [0, 2, 1], [0, 2, 1], [1, 0, 2], [1, 0, 2],
          [2, 0, 1], [2, 0, 1], [2, 0, 1], [1, 0, 2], [2, 0, 1]] v) →
        plurality.winners 3 10 P' univ univ = {2} ∧
        plurality.winners 3 10 P' univ {0, 1, 2, 5, 6} = {0} ∧
        plurality.winners 3 10 P' univ ({0, 1, 2, 5, 6} : Finset (Fin 10))ᶜ = {1} ∧
        twoStage .TP plurality P' {0, 1, 2, 5, 6} = {0}) ∧
    SusceptibleCC .TP plurality ∧ SusceptibleDC .TP plurality := by sorry

end HHRControl.PV
