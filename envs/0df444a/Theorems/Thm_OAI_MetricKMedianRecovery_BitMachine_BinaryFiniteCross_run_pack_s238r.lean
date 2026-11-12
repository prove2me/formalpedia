-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteCross_run_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.run_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:13:36.329203+00:00
-- url     : https://prove2.me/theorems/067dd224-8337-44c2-b035-a9b9b54da64c
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.run_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/ScanMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/ScanMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross`, with `open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence`, `open BinaryFiniteContext (labels setBits)`, `open BinaryFiniteMachine (historyBits)`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma run_pack_s238r {m d : ℕ} [PseudoMetricSpace (Label (Fin m))]
--       (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
--       (F B Q : Finset (Label (Fin m))) (v lam : ℚ) (eta : ℝ) (key spare k n q : ℕ)
--       (hc : CorrectCompletion loc F (v:ℝ) ((1+v^2)^q:ℚ) lam
--         (FiniteLabelContinuation.complete loc (rows distance) F v ((1+v^2)^q) lam))
--       (hv : (0:ℝ)<v) (hvsmall : (v:ℝ)<1/6) (hlam : (0:ℝ)<lam) (heta : 0≤eta)
--       (hQ : Q⊆F∪B) (hdis : Disjoint F B)
--       (hrow : ∀ i∈F,bidRow loc (1-3*(v:ℝ)) ((1+(v:ℝ)^2)^q) Q i≤lam)
--       (hfresh : ∀ i∈F,copy key i∉F∪B) (hco : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy key i))
--       (H G : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) (hHr : ∀ i∈H,i∈F) (hGr : ∀ i∈G,i∈F)
--       (hH : Valid loc F B Q v ((1+(v:ℝ)^2)^q) lam eta H) (hG : Valid loc F B Q v ((1+(v:ℝ)^2)^q) lam eta G) :
--       run (pack (BinaryFiniteContext.pack distance loc F Q v ((1+v^2)^q) lam) key spare k n q H G T U)=
--         BinaryCross.resultBits (FiniteLabelCrossing.run loc (rows distance) F Q v lam q n k (copy key) (copy spare) H G T U)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.bidRow` (definitions bundle `Q238L000` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder` (definitions bundle `Q238L019` of this split); `OAI.MetricKMedianRecovery.CanonicalMergePath.CorrectCompletion`, `OAI.MetricKMedianRecovery.FiniteLabelContinuation.complete`, `OAI.MetricKMedianRecovery.FiniteLabelCrossing.run`, `OAI.MetricKMedianRecovery.PhaseSequence.Valid` and `OAI.MetricKMedianRecovery.RationalLeaves.rows` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.resultBits` and `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.pack` (definitions bundle `Q238L025` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.copy` (definitions bundle `Q238L026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pack` (definitions bundle `Q238L029` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.run` (definitions bundle `Q238L049` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.run_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/ScanMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteCross.run_pack)

import Mathlib
import Definitions.Def_Q238L049

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteCross
open WordOperations WordList RationalLeaves CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] BinaryRegularChain.run BinaryScan.run
lemma run_pack_s238r {m d : ℕ} [PseudoMetricSpace (Label (Fin m))]
    (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F B Q : Finset (Label (Fin m))) (v lam : ℚ) (eta : ℝ) (key spare k n q : ℕ)
    (hc : CorrectCompletion loc F (v:ℝ) ((1+v^2)^q:ℚ) lam
      (FiniteLabelContinuation.complete loc (rows distance) F v ((1+v^2)^q) lam))
    (hv : (0:ℝ)<v) (hvsmall : (v:ℝ)<1/6) (hlam : (0:ℝ)<lam) (heta : 0≤eta)
    (hQ : Q⊆F∪B) (hdis : Disjoint F B)
    (hrow : ∀ i∈F,bidRow loc (1-3*(v:ℝ)) ((1+(v:ℝ)^2)^q) Q i≤lam)
    (hfresh : ∀ i∈F,copy key i∉F∪B) (hco : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy key i))
    (H G : List (Label (Fin m))) (T U : List (List (Label (Fin m)))) (hHr : ∀ i∈H,i∈F) (hGr : ∀ i∈G,i∈F)
    (hH : Valid loc F B Q v ((1+(v:ℝ)^2)^q) lam eta H) (hG : Valid loc F B Q v ((1+(v:ℝ)^2)^q) lam eta G) :
    run (pack (BinaryFiniteContext.pack distance loc F Q v ((1+v^2)^q) lam) key spare k n q H G T U)=
      BinaryCross.resultBits (FiniteLabelCrossing.run loc (rows distance) F Q v lam q n k (copy key) (copy spare) H G T U) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryFiniteCross

end OAI
end
