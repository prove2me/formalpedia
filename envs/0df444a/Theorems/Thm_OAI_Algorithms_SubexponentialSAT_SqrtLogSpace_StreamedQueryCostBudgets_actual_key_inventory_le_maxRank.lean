-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StreamedQueryCostBudgets_actual_key_inventory_le_maxRank
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets.actual_key_inventory_le_maxRank
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:21:58.717562+00:00
-- url     : https://prove2.me/theorems/14b31b2b-1b4e-4d69-903c-c104c5cee93e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets.actual_key_inventory_le_maxRank: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets.actual_key_inventory_le_maxRank` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/StreamedQueryCostBudgets.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/StreamedQueryCostBudgets.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets`, with `open scoped BigOperators`, `open OAI.Algorithms.SubexponentialSAT.SqrtLog SignatureTupleDFS SignatureTupleTraversal`, `open MulticolorTypes Subexp.ConstructivePacking LayoutExactBuckets`, `open Classical`):
--
--   ```lean
--   theorem actual_key_inventory_le_maxRank
--       {r Q D n : ℕ} {κ : Fin r → Type*}
--       (packing : PackingData (Fin D) (UniversalType r Q 1))
--       (owner : Fin D → Fin n) (A R B height : ℕ) (hAQ : A ≤ Q)
--       (hB : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
--       (hheight : B * LayoutProgram.constraintMassBound Q R ≤ height)
--       (rows : List (List Bool)) (low : List Bool) (nodes : Finset (Fin Q))
--       (t : Fin Q) (ht : t ∈ nodes)
--       (key : (g : Fin r) → Fin (2 ^ (LeafHeadSetupProgram.selectedHeads n rows low
--         (t.val*r+g.val)).length) → κ g)
--       (hkernel : ∀ g x y, key g x = key g y ↔
--         AttainedSignatures.integerKey (fun (j : Fin D)
--           (i : Fin (LeafHeadSetupProgram.selectedHeads n rows low (t.val*r+g.val)).length) =>
--             LayoutProducedMatrix.literalNat packing owner A R t j.val
--               ((LeafHeadSetupProgram.selectedHeads n rows low (t.val*r+g.val)).get i)) x =
--         AttainedSignatures.integerKey (fun (j : Fin D)
--           (i : Fin (LeafHeadSetupProgram.selectedHeads n rows low (t.val*r+g.val)).length) =>
--             LayoutProducedMatrix.literalNat packing owner A R t j.val
--               ((LeafHeadSetupProgram.selectedHeads n rows low (t.val*r+g.val)).get i)) y) :
--       (∏ g : Fin r, Fintype.card (AttainedSignatures.Representative (key g))) ≤
--         (2*n*height+1) ^ CostAssembly.maxTotalRank nodes
--           (BucketProgram.ProducedRank.actualRank packing owner A R rows low)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.selectedHeads` and `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssembly.maxTotalRank` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.constraintMassBound` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures.Representative` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix.literalNat` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.BucketProgram.ProducedRank.actualRank` (definitions bundle `OAIQ081S047` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures.integerKey` (definitions bundle `OAIQ081S114` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryStreamCorrect.node_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/StreamedQueryCostBudgets.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets.actual_key_inventory_le_maxRank)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S114

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog SignatureTupleDFS SignatureTupleTraversal
open MulticolorTypes Subexp.ConstructivePacking LayoutExactBuckets

noncomputable section
open Classical

theorem actual_key_inventory_le_maxRank
    {r Q D n : ℕ} {κ : Fin r → Type*}
    (packing : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (A R B height : ℕ) (hAQ : A ≤ Q)
    (hB : ∀ v, (Finset.univ.filter (fun i => owner i = v)).card ≤ B)
    (hheight : B * LayoutProgram.constraintMassBound Q R ≤ height)
    (rows : List (List Bool)) (low : List Bool) (nodes : Finset (Fin Q))
    (t : Fin Q) (ht : t ∈ nodes)
    (key : (g : Fin r) → Fin (2 ^ (LeafHeadSetupProgram.selectedHeads n rows low
      (t.val*r+g.val)).length) → κ g)
    (hkernel : ∀ g x y, key g x = key g y ↔
      AttainedSignatures.integerKey (fun (j : Fin D)
        (i : Fin (LeafHeadSetupProgram.selectedHeads n rows low (t.val*r+g.val)).length) =>
          LayoutProducedMatrix.literalNat packing owner A R t j.val
            ((LeafHeadSetupProgram.selectedHeads n rows low (t.val*r+g.val)).get i)) x =
      AttainedSignatures.integerKey (fun (j : Fin D)
        (i : Fin (LeafHeadSetupProgram.selectedHeads n rows low (t.val*r+g.val)).length) =>
          LayoutProducedMatrix.literalNat packing owner A R t j.val
            ((LeafHeadSetupProgram.selectedHeads n rows low (t.val*r+g.val)).get i)) y) :
    (∏ g : Fin r, Fintype.card (AttainedSignatures.Representative (key g))) ≤
      (2*n*height+1) ^ CostAssembly.maxTotalRank nodes
        (BucketProgram.ProducedRank.actualRank packing owner A R rows low) := by
  sorry

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets
end
