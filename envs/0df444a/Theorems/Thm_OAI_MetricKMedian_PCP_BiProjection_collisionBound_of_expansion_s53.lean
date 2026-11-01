-- Prove2me | Theorems.Thm_OAI_MetricKMedian_PCP_BiProjection_collisionBound_of_expansion_s53
-- name    : OAI.MetricKMedian.PCP.BiProjection.collisionBound_of_expansion_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:35:32.769313+00:00
-- url     : https://prove2.me/theorems/92e442f5-dde3-482e-8961-4a957bb2c554
-- title:
--   OAI.MetricKMedian.PCP.BiProjection.collisionBound_of_expansion_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.PCP.BiProjection.collisionBound_of_expansion` of [lean/OAI/Combinatorics/KMedian/Projection/Bound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Projection/Bound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.PCP.BiProjection`, with `open Finset`, `open scoped BigOperators Classical`):
--
--   ```lean
--   lemma collisionBound_of_expansion_s53 (s γ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
--       (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hs : G.Sound s) (hG : G.Expands γ) :
--       G.CollisionBound (1-γ*((1-s)/4)^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.PCP.BiProjection` and `OAI.MetricKMedian.PCP.BiProjection.CollisionBound` (definitions bundle `OAIQ053K009` of this split); `OAI.MetricKMedian.PCP.BiProjection.Expands` and `OAI.MetricKMedian.PCP.BiProjection.Sound` (definitions bundle `OAIQ053K024` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedian.PCP.Compiler.SeedProgram.good_bound_s53` and `OAI.MetricKMedian.PCP.ProjectionSeed.bad_bound_s53` of this split import it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Projection/Bound.lean (declaration OAI.MetricKMedian.PCP.BiProjection.collisionBound_of_expansion)

import Mathlib
import Definitions.Def_OAIQ053K024

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionBound

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
variable (G : BiProjection U V D S A B)

lemma collisionBound_of_expansion_s53 (s γ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hs : G.Sound s) (hG : G.Expands γ) :
    G.CollisionBound (1-γ*((1-s)/4)^2) := by
  sorry

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionBound

end OAI
end
