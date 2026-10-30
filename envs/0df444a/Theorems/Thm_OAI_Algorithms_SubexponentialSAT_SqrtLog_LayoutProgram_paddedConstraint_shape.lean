-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_paddedConstraint_shape
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.paddedConstraint_shape
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:09:35.9155+00:00
-- url     : https://prove2.me/theorems/7c218dd1-f2bb-4ab6-a8cf-53445257647c
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.paddedConstraint_shape: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.paddedConstraint_shape` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramPadded.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramPadded.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram`, with `open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking`):
--
--   ```lean
--   theorem paddedConstraint_shape
--       (P : PackingData I (UniversalType r Q 1))
--       (A R : ℕ) (denom : Oˣ)
--       (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
--       (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
--       (t : Fin Q) (g : Fin r) (v : I) :
--       paddedConstraint P A R t g v = 0 ∨
--         ∃ a, paddedConstraint P A R t g v =
--           LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
--             P.completeBlocks t g a
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` and `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData.blockCount` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.NodeUnits` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.denominator` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType`, `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeUniversalType` and `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData.completeBlocks` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBlocks.RowIndex` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBlocks.constraints` (definitions bundle `OAIQ081S054` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IncidenceHead` (definitions bundle `OAIQ081S056` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutUniversal.U` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.paddedConstraint` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutUniversal.data` (definitions bundle `OAIQ081S107` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix.literalHead_rank` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.literal_signature_eq` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProgramPadded.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.paddedConstraint_shape)

import Mathlib
import Definitions.Def_OAIQ081S107

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.Subexp.MatrixExtendedEntryProgram.instDecidableAnchorValid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking

variable {r Q : ℕ} {I O : Type*}
variable [Fintype I] [DecidableEq I] [CommRing O]

variable {node : Fin Q → O}

omit [Fintype I] in
theorem paddedConstraint_shape
    (P : PackingData I (UniversalType r Q 1))
    (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O) = (LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
    (t : Fin Q) (g : Fin r) (v : I) :
    paddedConstraint P A R t g v = 0 ∨
      ∃ a, paddedConstraint P A R t g v =
        LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
          P.completeBlocks t g a := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end
