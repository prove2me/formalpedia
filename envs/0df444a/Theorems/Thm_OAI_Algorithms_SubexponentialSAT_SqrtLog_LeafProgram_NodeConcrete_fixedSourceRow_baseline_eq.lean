-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_NodeConcrete_fixedSourceRow_baseline_eq
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.fixedSourceRow_baseline_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:08:31.514894+00:00
-- url     : https://prove2.me/theorems/570adc52-74c4-446f-bd61-a1dbef05038e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.fixedSourceRow_baseline_eq: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.fixedSourceRow_baseline_eq` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramNodeConcretePlan.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramNodeConcretePlan.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete`, with `open scoped BigOperators`, `open SubexponentialSAT.MulticolorTypes SubexponentialSAT.Subexp.ConstructivePacking`, `open LayoutProgram LayoutSourceRowsProgram PerturbationAssembly LayoutPullback`):
--
--   ```lean
--   theorem fixedSourceRow_baseline_eq (p : SourceBank.Parameters r Q d)
--       (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
--       (owner : Fin ps.length → Fin n) (howner : ∀ i,(ps.get i).1=(owner i).val)
--       (head : Fin Q → Fin n → Fin r)
--       (hhead : ∀ i t,(P.label i).head t=head t (owner i))
--       (f j : ℕ) (hj : (j,n+f)∈ps) (t : Fin Q) (x y : Fin n → ℤ)
--       (hown : ∀ v,head t v=(P.label (planIndex ps n f j hj)).slot 0 t → x v=y v)
--       (hother : ∀ g,g≠(P.label (planIndex ps n f j hj)).slot 0 t →
--         LayoutExactBuckets.signature (fun (k : Fin ps.length) (v : {v : Fin n //head t v=g}) =>
--           LayoutProducedMatrix.literalNat P owner p.aWord.length p.R t k.val v.val.val)
--           (fun v=>x v.val) =
--         LayoutExactBuckets.signature (fun (k : Fin ps.length) (v : {v : Fin n //head t v=g}) =>
--           LayoutProducedMatrix.literalNat P owner p.aWord.length p.R t k.val v.val.val)
--           (fun v=>y v.val)) :
--       (∑ v,(fixedSourceRow p ps P n f j v).eval (p.model.node p.t Q p.ht p.hfield t)*
--         (x v : p.model.O p.t)) =
--       ∑ v,(fixedSourceRow p ps P n f j v).eval (p.model.node p.t Q p.ht p.hfield t)*
--         (y v : p.model.O p.t)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutExactBuckets.signature` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.planIndex` (definitions bundle `OAIQ081S016` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProducedMatrix.literalNat` (definitions bundle `OAIQ081S047` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.node` (definitions bundle `OAIQ081S070` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.fixedSourceRow` (definitions bundle `OAIQ081S174` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryEmittedSourceTarget.signed_target` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramNodeConcretePlan.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete.fixedSourceRow_baseline_eq)

import Mathlib
import Definitions.Def_OAIQ081S174

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
open LayoutProgram LayoutSourceRowsProgram PerturbationAssembly LayoutPullback

variable {r Q d n : ℕ}

theorem fixedSourceRow_baseline_eq (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (owner : Fin ps.length → Fin n) (howner : ∀ i,(ps.get i).1=(owner i).val)
    (head : Fin Q → Fin n → Fin r)
    (hhead : ∀ i t,(P.label i).head t=head t (owner i))
    (f j : ℕ) (hj : (j,n+f)∈ps) (t : Fin Q) (x y : Fin n → ℤ)
    (hown : ∀ v,head t v=(P.label (planIndex ps n f j hj)).slot 0 t → x v=y v)
    (hother : ∀ g,g≠(P.label (planIndex ps n f j hj)).slot 0 t →
      LayoutExactBuckets.signature (fun (k : Fin ps.length) (v : {v : Fin n //head t v=g}) =>
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R t k.val v.val.val)
        (fun v=>x v.val) =
      LayoutExactBuckets.signature (fun (k : Fin ps.length) (v : {v : Fin n //head t v=g}) =>
        LayoutProducedMatrix.literalNat P owner p.aWord.length p.R t k.val v.val.val)
        (fun v=>y v.val)) :
    (∑ v,(fixedSourceRow p ps P n f j v).eval (p.model.node p.t Q p.ht p.hfield t)*
      (x v : p.model.O p.t)) =
    ∑ v,(fixedSourceRow p ps P n f j v).eval (p.model.node p.t Q p.ht p.hfield t)*
      (y v : p.model.O p.t) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafProgram.NodeConcrete

end

end OAI.Algorithms
end
