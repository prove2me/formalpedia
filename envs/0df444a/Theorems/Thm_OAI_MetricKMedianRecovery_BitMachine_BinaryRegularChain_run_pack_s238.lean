-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRegularChain_run_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain.run_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:13:11.819227+00:00
-- url     : https://prove2.me/theorems/f4466fa0-0baa-45b5-9b74-461772a553cf
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain.run_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/RegularChain.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/RegularChain.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain`, with `open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence`, `open BinaryFiniteContext (labels setBits)`, `open BinaryFiniteMachine (historyBits)`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma run_pack_s238 {m d : ℕ} [PseudoMetricSpace (Label (Fin m))]
--       (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
--       (F B Q : Finset (Label (Fin m))) (v z lam : ℚ) (eta : ℝ) (key spare : ℕ) (R : List (Label (Fin m)))
--       (hc : CorrectCompletion loc F (v:ℝ) z lam (FiniteLabelContinuation.complete loc (rows distance) F v z lam))
--       (hv : (0:ℝ)<v) (hvsmall : (v:ℝ)<1/6) (hz : (0:ℝ)<z) (hlam : (0:ℝ)<lam) (heta : 0≤eta)
--       (hQ : Q⊆F∪B) (hdis : Disjoint F B)
--       (hrow : ∀ i∈F,bidRow loc (1-3*(v:ℝ)) z Q i≤lam)
--       (hfresh : ∀ i∈F,copy key i∉F∪B) (hco : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy key i))
--       (H G : List (Label (Fin m))) (hHr : ∀ i∈H,i∈F) (hGr : ∀ i∈G,i∈F)
--       (hH : Valid loc F B Q v z lam eta H) (hG : Valid loc F B Q v z lam eta G) :
--       run (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key spare R H G)=
--         historyBits (CanonicalMergeRefinement.regularChain F R
--           (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) (copy spare) H G)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.bidRow` (definitions bundle `Q238K000` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.CanonicalMergePath.CorrectCompletion`, `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.regularChain` and `OAI.MetricKMedianRecovery.PhaseSequence.Valid` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder`, `OAI.MetricKMedianRecovery.RationalLeaves.rows` and `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.historyBits` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.FiniteLabelContinuation.complete` and `OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain.pack` (definitions bundle `Q238K022` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.copy` and `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pack` (definitions bundle `Q238K026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain.run` (definitions bundle `Q238K043` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.run_pack_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/RegularChain.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain.run_pack)

import Mathlib
import Definitions.Def_Q238K043

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRegularChain
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryRegular.run BinaryRefine.run
lemma run_pack_s238 {m d : ℕ} [PseudoMetricSpace (Label (Fin m))]
    (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F B Q : Finset (Label (Fin m))) (v z lam : ℚ) (eta : ℝ) (key spare : ℕ) (R : List (Label (Fin m)))
    (hc : CorrectCompletion loc F (v:ℝ) z lam (FiniteLabelContinuation.complete loc (rows distance) F v z lam))
    (hv : (0:ℝ)<v) (hvsmall : (v:ℝ)<1/6) (hz : (0:ℝ)<z) (hlam : (0:ℝ)<lam) (heta : 0≤eta)
    (hQ : Q⊆F∪B) (hdis : Disjoint F B)
    (hrow : ∀ i∈F,bidRow loc (1-3*(v:ℝ)) z Q i≤lam)
    (hfresh : ∀ i∈F,copy key i∉F∪B) (hco : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy key i))
    (H G : List (Label (Fin m))) (hHr : ∀ i∈H,i∈F) (hGr : ∀ i∈G,i∈F)
    (hH : Valid loc F B Q v z lam eta H) (hG : Valid loc F B Q v z lam eta G) :
    run (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key spare R H G)=
      historyBits (CanonicalMergeRefinement.regularChain F R
        (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) (copy spare) H G) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryRegularChain

end OAI
end
