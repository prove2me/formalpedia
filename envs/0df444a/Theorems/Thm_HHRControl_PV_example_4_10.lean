-- Prove2me | Theorems.Thm_HHRControl_PV_example_4_10
-- name    : HHRControl.PV.example_4_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-24T09:31:45.047101+00:00
-- url     : https://prove2.me/theorems/6c9d6a1c-71d5-48e0-87fc-b1eeb7eff22f
-- title:
--   Example 4.10, p. 12 — Condorcet voting is susceptible to destructive control by partition of voters
-- statement:
--   **Example 4.10.** Let $C=\{a,b,c\}$ and let $V$ consist of seven voters
--   $$v_1,v_2: c>a>b,\quad v_3: c>b>a,\quad v_4: b>a>c,\quad v_5: b>c>a,\quad v_6: a>b>c,\quad v_7: a>c>b.$$
--   Then $c$ is the Condorcet winner of $(C,V)$. For $V_1=\{v_1,v_7\}$ and $V_2=V-V_1$ there is no Condorcet winner of $(C,V_1)$ and $b$ is the Condorcet winner of $(C,V_2)$, so $c$ is not the unique winner of the two-stage election (in either tie-handling model). Consequently Condorcet voting is susceptible to destructive control by partition of voters.
--
--   This election witnesses the susceptibility part of the Condorcet clause of Theorem 3.6.
--
--   Differences from the source:
--   - encoding: candidates a, b, c; voters v1, v2, … → candidates 0, 1, 2 of Fin 3; voter vᵢ is index i − 1 of Fin n; reason: 0-based indices; no instance changes
--   - encoding: voters with the listed preference orders → every profile P whose ballots have the listed codes (rankingCode lists the candidates from most to least preferred); reason: rankingCode is injective, so this is exactly the listed profile; the profile exists
--   - encoding: Condorcet: the models TE and TP do not apply (p. 3) → stated for both tie rules; reason: a Condorcet winner is unique when it exists, so TE and TP nominate the same candidates and give the same two-stage election
-- source:
--   Hemaspaandra, Hemaspaandra & Rothe, Anyone but Him: The Complexity of Precluding an Alternative, arXiv:cs/0507027v5, p. 12, Example 4.10

import Mathlib
import Definitions.Def_HHRControl_PV_Elections

namespace HHRControl.PV

open Finset

/-- Example 4.10, p. 12: Condorcet voting is susceptible to destructive control by partition of
voters (in either tie-handling model). Candidates `a, b, c` are `0, 1, 2`; a ballot is given by
its code, the candidates from the most to the least preferred. -/
theorem example_4_10 :
    (∀ P : Fin 7 → Ranking 3,
      (∀ v, rankingCode (P v) =
        ![[2, 0, 1], [2, 0, 1], [2, 1, 0], [1, 0, 2], [1, 2, 0], [0, 1, 2], [0, 2, 1]] v) →
        condorcet.winners 3 7 P univ univ = {2} ∧
        condorcet.winners 3 7 P univ {0, 6} = ∅ ∧
        condorcet.winners 3 7 P univ ({0, 6} : Finset (Fin 7))ᶜ = {1} ∧
        ∀ rule : TieRule, twoStage rule condorcet P {0, 6} ≠ {2}) ∧
    ∀ rule : TieRule, SusceptibleDC rule condorcet := by sorry

end HHRControl.PV
