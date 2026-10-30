-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_BucketProgram_ProducedRank_actualMax_rank_budget
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualMax_rank_budget
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:44:38.832257+00:00
-- url     : https://prove2.me/theorems/d4213a8d-2c80-4fc9-9638-cb044661d7ed
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualMax_rank_budget: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualMax_rank_budget` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/BucketProgramProducedRankJoin.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/BucketProgramProducedRankJoin.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank`, with `open scoped BigOperators`, `open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking`, `open LeafHeadSetupProgram`):
--
--   ```lean
--   theorem actualMax_rank_budget {O : Type*} [CommRing O] {node : Fin Q → O}
--       (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin n)
--       (head : Fin Q → Fin n → Fin r)
--       (hhead : ∀ i t,(P.label i).head t=head t (owner i))
--       (R : ℕ) (denom : Oˣ) (hdenom : (denom : O)=(LayoutNumerator.denominator R : O))
--       (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
--       (rows : List (List Bool)) (low : List Bool) (nodes : Finset (Fin Q))
--       (hselected : ∀ t∈nodes,∀ (g : Fin r) (v : Fin n),
--         v.val∈selectedHeads n rows low (t.val*r+g.val)→head t v=g)
--       (m B : ℕ) (hB : 0 < B) (hD : D ≤ B*m)
--       (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4*R ≤ Q)
--       (hε : 0 < Asymptotic.layoutEpsilon m B)
--       (hwidth : 32*((Q-1 : ℕ):ℝ)*Real.log (2 / (Asymptotic.layoutEpsilon m B:ℝ)) ≤ (R:ℝ)^2)
--       (hcover : (1-Asymptotic.layoutEpsilon m B)*(D:ℚ) ≤
--         P.blockCount*(Fintype.card (UniversalType r Q 1):ℚ)) :
--       16 * (Asymptotic.layoutR m : ℝ) * (Asymptotic.L m : ℝ)^2 *
--         (CostAssembly.maxTotalRank nodes (actualRank P owner
--           (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R rows low) : ℝ) ≤ (m : ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.L`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.layoutEpsilon`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Asymptotic.layoutR`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.selectedHeads`, `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` and `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData.blockCount` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.maxTotalRank` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpRowInterpolation.NodeUnits` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutNumerator.denominator` (definitions bundle `OAIQ081S012` of this split); `OAI.Algorithms.SubexponentialSAT.Subexp.TailInterval.intervalStart` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` and `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeUniversalType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualRank` (definitions bundle `OAIQ081S047` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.ProducedQueryResources.rank_budget` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/BucketProgramProducedRankJoin.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualMax_rank_budget)

import Mathlib
import Definitions.Def_OAIQ081S014
import Definitions.Def_OAIQ081S047

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

noncomputable section
namespace SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LeafHeadSetupProgram

variable {r Q D n : ℕ}

theorem actualMax_rank_budget {O : Type*} [CommRing O] {node : Fin Q → O}
    (P : PackingData (Fin D) (UniversalType r Q 1)) (owner : Fin D → Fin n)
    (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (R : ℕ) (denom : Oˣ) (hdenom : (denom : O)=(LayoutNumerator.denominator R : O))
    (units : SubexponentialSAT.SubexpRowInterpolation.NodeUnits node)
    (rows : List (List Bool)) (low : List Bool) (nodes : Finset (Fin Q))
    (hselected : ∀ t∈nodes,∀ (g : Fin r) (v : Fin n),
      v.val∈selectedHeads n rows low (t.val*r+g.val)→head t v=g)
    (m B : ℕ) (hB : 0 < B) (hD : D ≤ B*m)
    (hr : 2 ≤ r) (hQ : 2 ≤ Q) (hR : 4 ≤ R) (hsize : 4*R ≤ Q)
    (hε : 0 < Asymptotic.layoutEpsilon m B)
    (hwidth : 32*((Q-1 : ℕ):ℝ)*Real.log (2 / (Asymptotic.layoutEpsilon m B:ℝ)) ≤ (R:ℝ)^2)
    (hcover : (1-Asymptotic.layoutEpsilon m B)*(D:ℚ) ≤
      P.blockCount*(Fintype.card (UniversalType r Q 1):ℚ)) :
    16 * (Asymptotic.layoutR m : ℝ) * (Asymptotic.L m : ℝ)^2 *
      (CostAssembly.maxTotalRank nodes (actualRank P owner
        (SubexponentialSAT.Subexp.TailInterval.intervalStart r Q R) R rows low) : ℝ) ≤ (m : ℝ) := by
  sorry

end SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank

end
end OAI.Algorithms
end
