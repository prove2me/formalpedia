-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryRegular_run_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryRegular.run_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:14:35.719778+00:00
-- url     : https://prove2.me/theorems/540edf61-ec67-4854-881b-1590915aea5b
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryRegular.run_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryRegular.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/MatchSize.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/MatchSize.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryRegular`, with `open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence`, `open BinaryFiniteContext (labels setBits)`, `open BinaryFiniteMachine (historyBits)`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma run_pack_s238r {m d : ℕ} [PseudoMetricSpace (Label (Fin m))]
--       (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
--       (F B Q : Finset (Label (Fin m))) (v z lam : ℚ) (eta : ℝ) (key : ℕ)
--       (hc : CorrectCompletion loc F (v:ℝ) z lam (FiniteLabelContinuation.complete loc (rows distance) F v z lam))
--       (hv : (0:ℝ)<v) (hvsmall : (v:ℝ)<1/6) (hz : (0:ℝ)<z) (hlam : (0:ℝ)<lam) (heta : 0≤eta)
--       (hQ : Q⊆F∪B) (hdis : Disjoint F B)
--       (hrow : ∀ i∈F,bidRow loc (1-3*(v:ℝ)) z Q i≤lam)
--       (hfresh : ∀ i∈F,copy key i∉F∪B) (hco : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy key i))
--       (H J : List (Label (Fin m))) (hHr : ∀ i∈H,i∈F) (hJr : ∀ i∈J,i∈F)
--       (hH : Valid loc F B Q v z lam eta H) (hJ : Valid loc F B Q v z lam eta J) :
--       run (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key H J)=
--         historyBits (regularPath (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) H J)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.bidRow` (definitions bundle `Q238L000` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.CanonicalMergePath.regularPath` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder` (definitions bundle `Q238L019` of this split); `OAI.MetricKMedianRecovery.CanonicalMergePath.CorrectCompletion`, `OAI.MetricKMedianRecovery.FiniteLabelContinuation.complete`, `OAI.MetricKMedianRecovery.PhaseSequence.Valid` and `OAI.MetricKMedianRecovery.RationalLeaves.rows` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.historyBits` (definitions bundle `Q238L025` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.copy` and `OAI.MetricKMedianRecovery.BitMachine.BinaryRegular.pack` (definitions bundle `Q238L026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pack` (definitions bundle `Q238L029` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRegular.run` (definitions bundle `Q238L049` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryRegularChain.run_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/MatchSize.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryRegular.run_pack)

import Mathlib
import Definitions.Def_Q238L049

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryRegular
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

lemma run_pack_s238r {m d : ℕ} [PseudoMetricSpace (Label (Fin m))]
    (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F B Q : Finset (Label (Fin m))) (v z lam : ℚ) (eta : ℝ) (key : ℕ)
    (hc : CorrectCompletion loc F (v:ℝ) z lam (FiniteLabelContinuation.complete loc (rows distance) F v z lam))
    (hv : (0:ℝ)<v) (hvsmall : (v:ℝ)<1/6) (hz : (0:ℝ)<z) (hlam : (0:ℝ)<lam) (heta : 0≤eta)
    (hQ : Q⊆F∪B) (hdis : Disjoint F B)
    (hrow : ∀ i∈F,bidRow loc (1-3*(v:ℝ)) z Q i≤lam)
    (hfresh : ∀ i∈F,copy key i∉F∪B) (hco : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy key i))
    (H J : List (Label (Fin m))) (hHr : ∀ i∈H,i∈F) (hJr : ∀ i∈J,i∈F)
    (hH : Valid loc F B Q v z lam eta H) (hJ : Valid loc F B Q v z lam eta J) :
    run (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key H J)=
      historyBits (regularPath (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) H J) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryRegular

end OAI
end
