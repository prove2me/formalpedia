-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalMergePath_advancePrefix_spec_s238
-- name    : OAI.MetricKMedianRecovery.CanonicalMergePath.advancePrefix_spec_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:18:14.359237+00:00
-- url     : https://prove2.me/theorems/7284bcd0-5db8-46ac-91ab-6287927e2b84
-- title:
--   OAI.MetricKMedianRecovery.CanonicalMergePath.advancePrefix_spec_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.CanonicalMergePath.advancePrefix_spec` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/MergePath.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/MergePath.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.CanonicalMergePath`, with `open PhaseSequence PhaseMergePath`):
--
--   ```lean
--    theorem advancePrefix_spec_s238 (loc : D → X) (F B Q : Finset X) (copy : X → X)
--       (v z lam eta : ℝ) (complete : Finset X → List X)
--       (hc : CorrectCompletion loc F v z lam complete)
--       (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z)
--       (hlam : 0 < lam) (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B)
--       (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
--       (C U : List X) (i : X) (hiF : i ∈ F) (hiB : i ∉ B)
--       (hfresh : copy i ∉ F ∪ B) (hco : ∀ j, dist (loc j) i = dist (loc j) (copy i))
--       (hC : Prefix loc F B v z lam eta Q C)
--       (hi : Entry loc F B (Q ∪ C.toFinset) v z lam eta i)
--       (hCr : ∀ k ∈ C, k ∈ F) (hUr : ∀ k ∈ U, k ∈ F)
--       (hcur : Valid loc F B Q v z lam eta (C++U)) :
--       let r := advancePrefix complete Q copy C U i
--       (∀ k ∈ r.1, k ∈ F) ∧ Valid loc F B Q v z lam eta (C++i::r.1) ∧
--         Path loc F B Q copy v z lam eta (C++U) r.2 (C++i::r.1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.bidRow` (definitions bundle `Q238K000` of this split); `OAI.MetricKMedianRecovery.CanonicalMergePath.advancePrefix` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.CanonicalMergePath.CorrectCompletion`, `OAI.MetricKMedianRecovery.CanonicalMergePath.Path`, `OAI.MetricKMedianRecovery.PhaseSequence.Entry`, `OAI.MetricKMedianRecovery.PhaseSequence.Prefix` and `OAI.MetricKMedianRecovery.PhaseSequence.Valid` (definitions bundle `Q238K014` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.run_pack_s238` and `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.regularChain_spec_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/MergePath.lean (declaration OAI.MetricKMedianRecovery.CanonicalMergePath.advancePrefix_spec)

import Mathlib
import Definitions.Def_Q238K014

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergePath
open PhaseSequence PhaseMergePath
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

 theorem advancePrefix_spec_s238 (loc : D → X) (F B Q : Finset X) (copy : X → X)
    (v z lam eta : ℝ) (complete : Finset X → List X)
    (hc : CorrectCompletion loc F v z lam complete)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z)
    (hlam : 0 < lam) (heta : 0 ≤ eta) (hQ : Q ⊆ F ∪ B)
    (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (C U : List X) (i : X) (hiF : i ∈ F) (hiB : i ∉ B)
    (hfresh : copy i ∉ F ∪ B) (hco : ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (hC : Prefix loc F B v z lam eta Q C)
    (hi : Entry loc F B (Q ∪ C.toFinset) v z lam eta i)
    (hCr : ∀ k ∈ C, k ∈ F) (hUr : ∀ k ∈ U, k ∈ F)
    (hcur : Valid loc F B Q v z lam eta (C++U)) :
    let r := advancePrefix complete Q copy C U i
    (∀ k ∈ r.1, k ∈ F) ∧ Valid loc F B Q v z lam eta (C++i::r.1) ∧
      Path loc F B Q copy v z lam eta (C++U) r.2 (C++i::r.1) := by
  sorry

end MetricKMedianRecovery.CanonicalMergePath

end OAI
end
