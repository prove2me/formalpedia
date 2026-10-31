-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_NodeConcrete_literal_signature_eq
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.literal_signature_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:49:47.731287+00:00
-- url     : https://prove2.me/theorems/49e5fbb3-49a7-43bb-a7cc-b31f98487acb
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.literal_signature_eq: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.literal_signature_eq` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramNodeConcreteLocality.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramNodeConcreteLocality.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete`, with `open scoped BigOperators`, `open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking`, `open LayoutProgram LayoutExactBuckets LayoutPullback`):
--
--   ```lean
--   theorem literal_signature_eq (p : SourceBank.Parameters r Q d)
--       (P : PackingData (Fin D) (UniversalType r Q 1))
--       (owner : Fin D → Fin n) (head : Fin Q → Fin n → Fin r)
--       (hhead : ∀ i t,(P.label i).head t=head t (owner i))
--       (t : Fin Q) (g : Fin r) (x y : {v : Fin n //head t v=g} → ℤ)
--       (hxy : signature (fun (j : Fin D) v => LayoutProducedMatrix.literalNat P owner
--         p.aWord.length p.R t j.val v.val.val) x =
--         signature (fun (j : Fin D) v => LayoutProducedMatrix.literalNat P owner
--         p.aWord.length p.R t j.val v.val.val) y) :
--       (pulled p P owner head hhead).bucketLabel t g x =
--         (pulled p P owner head hhead).bucketLabel t g y
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutExactBuckets.signature` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix.literalNat` (definitions bundle `OAIQ081S047` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Layout.Data.bucketLabel` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Layout.Data` (definitions bundle `OAIQ081S054` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.pulled` (definitions bundle `OAIQ081S169` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.fixedSourceRow_baseline_eq` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramNodeConcreteLocality.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.literal_signature_eq)

import Mathlib
import Definitions.Def_OAIQ081S169

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete
open scoped BigOperators
open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking
open LayoutProgram LayoutExactBuckets LayoutPullback

variable {r Q d D n : ℕ}

theorem literal_signature_eq (p : SourceBank.Parameters r Q d)
    (P : PackingData (Fin D) (UniversalType r Q 1))
    (owner : Fin D → Fin n) (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (t : Fin Q) (g : Fin r) (x y : {v : Fin n //head t v=g} → ℤ)
    (hxy : signature (fun (j : Fin D) v => LayoutProducedMatrix.literalNat P owner
      p.aWord.length p.R t j.val v.val.val) x =
      signature (fun (j : Fin D) v => LayoutProducedMatrix.literalNat P owner
      p.aWord.length p.R t j.val v.val.val) y) :
    (pulled p P owner head hhead).bucketLabel t g x =
      (pulled p P owner head hhead).bucketLabel t g y := by
  sorry

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end
