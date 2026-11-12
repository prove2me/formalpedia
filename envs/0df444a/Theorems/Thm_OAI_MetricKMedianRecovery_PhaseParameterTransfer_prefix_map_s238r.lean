-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_PhaseParameterTransfer_prefix_map_s238r
-- name    : OAI.MetricKMedianRecovery.PhaseParameterTransfer.prefix_map_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:30:00.994984+00:00
-- url     : https://prove2.me/theorems/ab9936d7-0646-49d9-88b4-4e3dfbc73c13
-- title:
--   OAI.MetricKMedianRecovery.PhaseParameterTransfer.prefix_map_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.PhaseParameterTransfer.prefix_map` of [lean/OAI/Combinatorics/KMedianRecovery/Strictness/OpenableMap.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Strictness/OpenableMap.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.PhaseParameterTransfer`):
--
--   ```lean
--   theorem prefix_map_s238r (loc : D → X) (F B Q : Finset X) (H : List X) (r : X → X)
--       (v z lam lam' eta eps : ℝ) (hv : 0 < v) (hvsmall : v < 1/6)
--       (heps : 0 ≤ eps) (hprice : lam ≤ lam')
--       (herror : lam'-lam+(Fintype.card D:ℝ)*((1-3*v)*eps) ≤ (Fintype.card D:ℝ)*eta)
--       (hinj : Function.Injective r) (hfix : ∀ i ∈ F, r i = i)
--       (hshrink : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) (r x) ≤ dist (loc j) x)
--       (hloss : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) x ≤ dist (loc j) (r x)+eps)
--       (hp : PhaseSequence.Prefix loc F B v z lam 0 Q H) :
--       PhaseSequence.Prefix loc F (B.image r) v z lam' eta (Q.image r) (H.map r)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.PhaseSequence.Prefix` (definitions bundle `Q238L010` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.PhaseParameterAlignment.align_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Strictness/OpenableMap.lean (declaration OAI.MetricKMedianRecovery.PhaseParameterTransfer.prefix_map)

import Mathlib
import Definitions.Def_Q238L010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.PhaseParameterTransfer
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

theorem prefix_map_s238r (loc : D → X) (F B Q : Finset X) (H : List X) (r : X → X)
    (v z lam lam' eta eps : ℝ) (hv : 0 < v) (hvsmall : v < 1/6)
    (heps : 0 ≤ eps) (hprice : lam ≤ lam')
    (herror : lam'-lam+(Fintype.card D:ℝ)*((1-3*v)*eps) ≤ (Fintype.card D:ℝ)*eta)
    (hinj : Function.Injective r) (hfix : ∀ i ∈ F, r i = i)
    (hshrink : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) (r x) ≤ dist (loc j) x)
    (hloss : ∀ j, ∀ x ∈ F ∪ B, dist (loc j) x ≤ dist (loc j) (r x)+eps)
    (hp : PhaseSequence.Prefix loc F B v z lam 0 Q H) :
    PhaseSequence.Prefix loc F (B.image r) v z lam' eta (Q.image r) (H.map r) := by
  sorry

end MetricKMedianRecovery.PhaseParameterTransfer

end OAI
end
