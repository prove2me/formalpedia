-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_Packing_incidence_mean_jointScore_le
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.incidence_mean_jointScore_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:55:04.428108+00:00
-- url     : https://prove2.me/theorems/f16b21c6-f5e2-4e62-83c7-bbc4336684cf
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.incidence_mean_jointScore_le: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.incidence_mean_jointScore_le` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingSelection.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingSelection.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing`, with `open scoped BigOperators`, `open SubexponentialSAT.Variance SubexponentialSAT.MulticolorTypes`):
--
--   ```lean
--   theorem incidence_mean_jointScore_le (ε : ℚ) (_hε : 0 < ε) (B a : ℕ)
--       (hB : ∀ v, (Finset.univ.filter fun i => ivar i = v).card ≤ B)
--       (ha : ∀ e, (Finset.univ.filter fun i => factor i = e).card ≤ a)
--       (hM : 0 < Fintype.card I) (hn : 0 < Fintype.card V)
--       (hlarge : 4*((B+a : ℕ) : ℚ)*(Fintype.card (UniversalType r Q 1) : ℚ)^2 ≤
--         ε^2*(Fintype.card I : ℚ))
--       (hhead : 16*(Q : ℚ)*(r : ℚ)^2 ≤ (Fintype.card V : ℚ)) :
--       mean uniformWeight (jointScore
--         (fun ω : WordAssignment V E r Q => energy (incidenceType ivar factor ω))
--         headEnergy (ε*(Fintype.card I : ℚ)/(Fintype.card (UniversalType r Q 1) : ℚ))
--         ((Fintype.card V : ℚ)/(2*(r : ℚ)))) ≤
--         (ε*(Fintype.card I : ℚ)/(Fintype.card (UniversalType r Q 1) : ℚ))^2 *
--         ((Fintype.card V : ℚ)/(2*(r : ℚ)))^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.Word` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.Variance.mean`, `OAI.Algorithms.SubexponentialSAT.Variance.uniformWeight`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.energy` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.jointScore` (definitions bundle `OAIQ081S018` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType`, `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeUniversalType` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.WordAssignment` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.incidenceType` (definitions bundle `OAIQ081S047` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.headEnergy` (definitions bundle `OAIQ081S078` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedHeads.problem_computed_energies` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/PackingSelection.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.incidence_mean_jointScore_le)

import Mathlib
import Definitions.Def_OAIQ081S078

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.compatibleDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryKernel.spectatorsAgreeDecidable _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Packing
open scoped BigOperators
open SubexponentialSAT.Variance SubexponentialSAT.MulticolorTypes
noncomputable section

section Incidences
variable {I V E : Type*} [Fintype I] [Fintype V] [Fintype E]
  [DecidableEq I] [DecidableEq V] [DecidableEq E]
variable (ivar : I → V) (factor : I → E) {r Q : ℕ} [NeZero r]

theorem incidence_mean_jointScore_le (ε : ℚ) (_hε : 0 < ε) (B a : ℕ)
    (hB : ∀ v, (Finset.univ.filter fun i => ivar i = v).card ≤ B)
    (ha : ∀ e, (Finset.univ.filter fun i => factor i = e).card ≤ a)
    (hM : 0 < Fintype.card I) (hn : 0 < Fintype.card V)
    (hlarge : 4*((B+a : ℕ) : ℚ)*(Fintype.card (UniversalType r Q 1) : ℚ)^2 ≤
      ε^2*(Fintype.card I : ℚ))
    (hhead : 16*(Q : ℚ)*(r : ℚ)^2 ≤ (Fintype.card V : ℚ)) :
    mean uniformWeight (jointScore
      (fun ω : WordAssignment V E r Q => energy (incidenceType ivar factor ω))
      headEnergy (ε*(Fintype.card I : ℚ)/(Fintype.card (UniversalType r Q 1) : ℚ))
      ((Fintype.card V : ℚ)/(2*(r : ℚ)))) ≤
      (ε*(Fintype.card I : ℚ)/(Fintype.card (UniversalType r Q 1) : ℚ))^2 *
      ((Fintype.card V : ℚ)/(2*(r : ℚ)))^2 := by
  sorry

end Incidences
end
end SubexponentialSAT.SqrtLog.Packing

end OAI.Algorithms
end
