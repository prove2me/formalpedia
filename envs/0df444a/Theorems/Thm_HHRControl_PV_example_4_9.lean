-- Prove2me | Theorems.Thm_HHRControl_PV_example_4_9
-- name    : HHRControl.PV.example_4_9
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:36.878137+00:00
-- url     : https://prove2.me/theorems/dacd5eb7-5f68-40a0-bcbe-85f66f344c58
-- title:
--   Example 4.9, p. 12 — plurality is susceptible to constructive and destructive control by partition of voters in model TE
-- statement:
--   **Example 4.9.** Let $C=\{a,b,c\}$ and let $V$ consist of five voters
--   $$v_1: a>b>c,\quad v_2: a>b>c,\quad v_3: b>a>c,\quad v_4: b>a>c,\quad v_5: c>a>b.$$
--   Then $c$ is not a plurality winner of $(C,V)$. For $V_1=\{v_5\}$ and $V_2=V-V_1$, $c$ is the unique plurality winner of $(C,V_1)$, $a$ and $b$ tie for winner of $(C,V_2)$, and in model TE $c$ is the unique winner of the two-stage election.
--
--   For the destructive case let $V'=\{v_1,v_2,v_3,v_5\}$. Then $a$ is the unique plurality winner of $(C,V')$, and for $V'_1=\{v_1,v_3\}$, $V'_2=\{v_2,v_5\}$ neither subcommittee nominates a candidate in model TE, so $a$ is not the unique winner of the two-stage election.
--
--   Consequently plurality voting is susceptible to constructive and to destructive control by partition of voters in model TE.
--
--   These elections witness the susceptibility part of the plurality TE clauses of Theorem 3.6.
--
--   Differences from the source:
--   - encoding: candidates a, b, c; voters v1, v2, … → candidates 0, 1, 2 of Fin 3; voter vᵢ is index i − 1 of Fin 5; in the election (C, V′) the voters v1, v2, v3, v5 are indices 0–3 of Fin 4; reason: 0-based indices; no instance changes
--   - encoding: voters with the listed preference orders → every profile P whose ballots have the listed codes (rankingCode lists the candidates from most to least preferred); reason: rankingCode is injective, so this is exactly the listed profile; the profile exists
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, arXiv:cs/0507027v5, p. 12, Example 4.9

import Mathlib
import Definitions.Def_HHRControl_PV_Elections

namespace HHRControl.PV

open Finset

/-- Example 4.9, p. 12: plurality voting is susceptible to constructive and to destructive control
by partition of voters in model TE. Candidates `a, b, c` are `0, 1, 2`; a ballot is given by its
code, the candidates from the most to the least preferred. -/
theorem example_4_9 :
    (∀ P : Fin 5 → Ranking 3,
      (∀ v, rankingCode (P v) = ![[0, 1, 2], [0, 1, 2], [1, 0, 2], [1, 0, 2], [2, 0, 1]] v) →
        (2 : Fin 3) ∉ plurality.winners 3 5 P univ univ ∧
        plurality.winners 3 5 P univ {4} = {2} ∧
        plurality.winners 3 5 P univ ({4} : Finset (Fin 5))ᶜ = {0, 1} ∧
        twoStage .TE plurality P {4} = {2}) ∧
    (∀ P' : Fin 4 → Ranking 3,
      (∀ v, rankingCode (P' v) = ![[0, 1, 2], [0, 1, 2], [1, 0, 2], [2, 0, 1]] v) →
        plurality.winners 3 4 P' univ univ = {0} ∧
        nominees .TE plurality P' {0, 2} = ∅ ∧
        nominees .TE plurality P' ({0, 2} : Finset (Fin 4))ᶜ = ∅ ∧
        twoStage .TE plurality P' {0, 2} ≠ {0}) ∧
    SusceptibleCC .TE plurality ∧ SusceptibleDC .TE plurality := by sorry

end HHRControl.PV
