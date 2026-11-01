-- Prove2me | Theorems.Thm_OAI_MetricKMedian_PCP_BiProjection_collision_sound_s53
-- name    : OAI.MetricKMedian.PCP.BiProjection.collision_sound_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:35:56.804995+00:00
-- url     : https://prove2.me/theorems/e2cbd9eb-7d7f-4bd2-b483-da8ddd731bdc
-- title:
--   OAI.MetricKMedian.PCP.BiProjection.collision_sound_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.PCP.BiProjection.collision_sound` of [lean/OAI/Combinatorics/KMedian/Projection/Rounding.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Projection/Rounding.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.PCP.BiProjection`, with `open Finset`, `open scoped BigOperators Classical`):
--
--   ```lean
--   lemma collision_sound_s53 {T : Type} [Fintype T] (s : ℝ) (hs : G.Sound s)
--       (f : U → A → T → ℝ) (hf : ∀ u a t, 0 ≤ f u a t)
--       (H : T → ℝ) (hH : ∀ t, 0 ≤ H t) (ht : ∀ u t, ∑ a, f u a t=H t) :
--       G.collision f ≤ s * ∑ t, H t^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.PCP.BiProjection` and `OAI.MetricKMedian.PCP.BiProjection.collision` (definitions bundle `OAIQ053K009` of this split); `OAI.MetricKMedian.PCP.BiProjection.Sound` (definitions bundle `OAIQ053K024` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.PCP.BiProjection.collisionBound_of_expansion_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Projection/Rounding.lean (declaration OAI.MetricKMedian.PCP.BiProjection.collision_sound)

import Mathlib
import Definitions.Def_OAIQ053K024

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPProjectionRounding

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators Classical

namespace BiProjection
variable {U V D S A B : Type}
variable [Fintype U] [Fintype V] [Fintype D] [Fintype S] [Fintype A] [Fintype B]
variable [Nonempty U] [Nonempty V] [Nonempty D] [Nonempty S] [Nonempty A] [Nonempty B]
variable (G : BiProjection U V D S A B)

omit [Nonempty U] [Nonempty V] [Nonempty D] in
lemma collision_sound_s53 {T : Type} [Fintype T] (s : ℝ) (hs : G.Sound s)
    (f : U → A → T → ℝ) (hf : ∀ u a t, 0 ≤ f u a t)
    (H : T → ℝ) (hH : ∀ t, 0 ≤ H t) (ht : ∀ u t, ∑ a, f u a t=H t) :
    G.collision f ≤ s * ∑ t, H t^2 := by
  sorry

end BiProjection
end MetricKMedian.PCP

end Inline_PCPProjectionRounding

end OAI
end
