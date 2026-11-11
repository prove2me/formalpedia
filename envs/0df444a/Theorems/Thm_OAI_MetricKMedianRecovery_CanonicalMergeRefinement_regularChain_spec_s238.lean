-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalMergeRefinement_regularChain_spec_s238
-- name    : OAI.MetricKMedianRecovery.CanonicalMergeRefinement.regularChain_spec_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:18:55.06502+00:00
-- url     : https://prove2.me/theorems/1fce6c42-d7ae-4a4a-9a53-4b2772a42e89
-- title:
--   OAI.MetricKMedianRecovery.CanonicalMergeRefinement.regularChain_spec_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.regularChain_spec` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/MergeRefine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/MergeRefine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.CanonicalMergeRefinement`, with `open PhaseSequence PhaseMergePath PhaseMergeRefinement`):
--
--   ```lean
--    theorem regularChain_spec_s238 (loc : D → X) (F B Q : Finset X) (R : List X) (copy spare : X → X)
--       (v z lam eta : ℝ) (complete : Finset X → List X)
--       (hcomplete : CanonicalMergePath.CorrectCompletion loc F v z lam complete)
--       (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
--       (heta : 0 ≤ eta) (hR : ∀ i∈F,i∈R) (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B)
--       (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
--       (hc : ∀ i ∈ F, copy i ∉ F ∪ B)
--       (hd : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (copy i))
--       (hs : ∀ i ∈ F, spare i ∉ F ∪ pool F B copy)
--       (he : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (spare i))
--       (H G : List X) (hH : Valid loc F B Q v z lam eta H)
--       (hG : Valid loc F B Q v z lam eta G)
--       (hHr : ∀ i ∈ H, i ∈ F) (hGr : ∀ i ∈ G, i ∈ F) :
--       let T := regularChain F R complete Q copy spare H G
--       T.length ≤ F.card*(F.card+3)*(F.card+2) ∧
--         EPath loc F (pool F (pool F B copy) spare) Q v z lam eta H T G
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.bidRow` (definitions bundle `Q238K000` of this split); `OAI.MetricKMedianRecovery.PhaseMergePath.pool` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.CanonicalMergePath.CorrectCompletion`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.EPath`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.regularChain` and `OAI.MetricKMedianRecovery.PhaseSequence.Valid` (definitions bundle `Q238K014` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.FiniteLabelCrossing.run_spec_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/MergeRefine.lean (declaration OAI.MetricKMedianRecovery.CanonicalMergeRefinement.regularChain_spec)

import Mathlib
import Definitions.Def_Q238K014

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalMergeRefinement
open PhaseSequence PhaseMergePath PhaseMergeRefinement
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

 theorem regularChain_spec_s238 (loc : D → X) (F B Q : Finset X) (R : List X) (copy spare : X → X)
    (v z lam eta : ℝ) (complete : Finset X → List X)
    (hcomplete : CanonicalMergePath.CorrectCompletion loc F v z lam complete)
    (hv : 0 < v) (hvsmall : v < 1/6) (hz : 0 < z) (hlam : 0 < lam)
    (heta : 0 ≤ eta) (hR : ∀ i∈F,i∈R) (hQ : Q ⊆ F ∪ B) (hdis : Disjoint F B)
    (hrow : ∀ k ∈ F, bidRow loc (1-3*v) z Q k ≤ lam)
    (hc : ∀ i ∈ F, copy i ∉ F ∪ B)
    (hd : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (copy i))
    (hs : ∀ i ∈ F, spare i ∉ F ∪ pool F B copy)
    (he : ∀ i ∈ F, ∀ j, dist (loc j) i = dist (loc j) (spare i))
    (H G : List X) (hH : Valid loc F B Q v z lam eta H)
    (hG : Valid loc F B Q v z lam eta G)
    (hHr : ∀ i ∈ H, i ∈ F) (hGr : ∀ i ∈ G, i ∈ F) :
    let T := regularChain F R complete Q copy spare H G
    T.length ≤ F.card*(F.card+3)*(F.card+2) ∧
      EPath loc F (pool F (pool F B copy) spare) Q v z lam eta H T G := by
  sorry

end MetricKMedianRecovery.CanonicalMergeRefinement

end OAI
end
