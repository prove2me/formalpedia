-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProducedMatrix_literalHead_rank
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix.literalHead_rank
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:08:40.90845+00:00
-- url     : https://prove2.me/theorems/7dc13482-3ded-419b-ba9b-0f017ebbde4b
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix.literalHead_rank: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix.literalHead_rank` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProducedMatrix.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProducedMatrix.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix`, with `open scoped BigOperators`, `open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking`, `open LayoutPullback LayoutExactBuckets LayoutProgram`):
--
--   ```lean
--   theorem literalHead_rank (P : PackingData I (UniversalType r Q 1))
--       (owner : I → V) (head : Fin Q → V → Fin r)
--       (hhead : ∀ i t,(P.label i).head t=head t (owner i))
--       (A R : ℕ) (denom : Oˣ)
--       (hdenom : (denom : O)=(LayoutNumerator.denominator R : O))
--       (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q) (g : Fin r) :
--       LayoutRank.rowRank (fun j (v : {v : V // head t v=g}) =>
--         literalMatrix P owner A R t j v.val) =
--       LayoutRank.rowRank (pulledConstraints (headOwner P owner head hhead t g)
--         (LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
--           P.completeBlocks t g))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank.rowRank`, `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` and `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData.blockCount` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.NodeUnits` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.denominator` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType`, `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeUniversalType`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix.literalMatrix` and `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData.completeBlocks` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutExactBuckets.pulledConstraints` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBlocks.RowIndex` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBlocks.constraints` (definitions bundle `OAIQ081S054` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix.headOwner` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.IncidenceHead` (definitions bundle `OAIQ081S056` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutUniversal.U` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutUniversal.data` (definitions bundle `OAIQ081S107` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualRank_sum_le` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutProducedMatrix.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix.literalHead_rank)

import Mathlib
import Definitions.Def_OAIQ081S107

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutProducedMatrix
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutPullback LayoutExactBuckets LayoutProgram

variable {r Q : ℕ} {I V O : Type*}
variable [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [CommRing O]
variable {node : Fin Q → O}

theorem literalHead_rank (P : PackingData I (UniversalType r Q 1))
    (owner : I → V) (head : Fin Q → V → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (A R : ℕ) (denom : Oˣ)
    (hdenom : (denom : O)=(LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node) (t : Fin Q) (g : Fin r) :
    LayoutRank.rowRank (fun j (v : {v : V // head t v=g}) =>
      literalMatrix P owner A R t j v.val) =
    LayoutRank.rowRank (pulledConstraints (headOwner P owner head hhead t g)
      (LayoutBlocks.constraints (LayoutUniversal.data A R denom hdenom units)
        P.completeBlocks t g)) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutProducedMatrix

end OAI.Algorithms
end
