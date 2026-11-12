-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryMatch_run_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.run_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:15:29.73803+00:00
-- url     : https://prove2.me/theorems/0362bbe4-ba2b-4918-9714-04c128890445
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.run_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/MatchSize.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/MatchSize.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch`, with `open WordOperations WordList RationalLeaves CanonicalMatch CanonicalMergePath PhaseSequence`, `open BinaryFiniteContext (labels setBits)`, `open BinaryFiniteMachine (historyBits)`):
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
--       (C U T : List (Label (Fin m))) (hCr : ∀ i∈C,i∈F) (hUr : ∀ i∈U,i∈F) (hTr : ∀ i∈T,i∈F)
--       (htarget : Prefix loc F B v z lam eta Q (C++T)) (hcur : Valid loc F B Q v z lam eta (C++U)) :
--       run (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key F C U T)=
--         accBits ⟨C++T,(matchPrefix (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) C U T).1,
--           (matchPrefix (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) C U T).2⟩
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.bidRow` (definitions bundle `Q238L000` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.CanonicalMatch.Acc` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.CanonicalMergePath.matchPrefix` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.PhaseSequence.Prefix` (definitions bundle `Q238L010` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder` (definitions bundle `Q238L019` of this split); `OAI.MetricKMedianRecovery.CanonicalMergePath.CorrectCompletion`, `OAI.MetricKMedianRecovery.FiniteLabelContinuation.complete`, `OAI.MetricKMedianRecovery.PhaseSequence.Valid` and `OAI.MetricKMedianRecovery.RationalLeaves.rows` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.copy` (definitions bundle `Q238L026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pack` (definitions bundle `Q238L029` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.accBits` and `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.pack` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.run` (definitions bundle `Q238L049` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryRegular.run_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/MatchSize.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.run_pack)

import Mathlib
import Definitions.Def_Q238L049

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMatch
open WordOperations WordList RationalLeaves CanonicalMatch CanonicalMergePath PhaseSequence
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)

lemma run_pack_s238r {m d : ℕ} [PseudoMetricSpace (Label (Fin m))]
    (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F B Q : Finset (Label (Fin m))) (v z lam : ℚ) (eta : ℝ) (key : ℕ)
    (hc : CorrectCompletion loc F (v:ℝ) z lam (FiniteLabelContinuation.complete loc (rows distance) F v z lam))
    (hv : (0:ℝ)<v) (hvsmall : (v:ℝ)<1/6) (hz : (0:ℝ)<z) (hlam : (0:ℝ)<lam) (heta : 0≤eta)
    (hQ : Q⊆F∪B) (hdis : Disjoint F B)
    (hrow : ∀ i∈F,bidRow loc (1-3*(v:ℝ)) z Q i≤lam)
    (hfresh : ∀ i∈F,copy key i∉F∪B) (hco : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy key i))
    (C U T : List (Label (Fin m))) (hCr : ∀ i∈C,i∈F) (hUr : ∀ i∈U,i∈F) (hTr : ∀ i∈T,i∈F)
    (htarget : Prefix loc F B v z lam eta Q (C++T)) (hcur : Valid loc F B Q v z lam eta (C++U)) :
    run (pack (BinaryFiniteContext.pack distance loc F Q v z lam) key F C U T)=
      accBits ⟨C++T,(matchPrefix (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) C U T).1,
        (matchPrefix (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) C U T).2⟩ := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryMatch

end OAI
end
