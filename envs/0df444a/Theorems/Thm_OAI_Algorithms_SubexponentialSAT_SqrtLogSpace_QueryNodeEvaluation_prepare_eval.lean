-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryNodeEvaluation_prepare_eval
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_eval
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:33:45.035014+00:00
-- url     : https://prove2.me/theorems/afbf1691-3054-4c42-8b52-186245729fad
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_eval: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_eval` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeEvaluation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeEvaluation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation`, with `open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage`, `open LeafHeadSetupProgram QueryTupleState`):
--
--   ```lean
--   theorem prepare_eval (s : Native.Inputs) (a : Data)
--       (bits : List Bool) (tail : List (List Bool))
--       (H : Finset (Fin s.n)) (J B : ℕ)
--       (hsource : NativeLayoutLoad.SourceBank s a)
--       (hcursor : a.stacks 301=Encoding.encodeList id (bits::tail))
--       (hmask : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
--       (horder : a.stacks 243=List.replicate J true)
--       (hb : WordBound B a) (hcap : SignatureHeadLoader.bootstrapOutputBound s ≤ B) :
--       ∃ ra rd rc words ticks b,
--         CacheCorrect s.height (unary s.R) s.width words ∧
--         Eval prepareNode ticks a b ∧ ticks ≤ 20000*(B+1)^4+300*(B+1) ∧
--         WordBound B b ∧
--         Native.Ready s (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort b) ∧
--         b.stacks 832=List.replicate (s.n-H.card) true ∧ b.stacks 833=List.replicate J true ∧
--         b.stacks 834=[] ∧ b.stacks 835=[] ∧ b.stacks 850=[] ∧ b.stacks 851=[] ∧
--         (∀ i ∈ PairNativeSetup.scratch,b.stacks i=[]) ∧
--         (∀ i, i ∉ PairNativeSetup.scratch → i ≠ 832 → i ≠ 833 → i ≠ 834 → i ≠ 835 →
--           b.stacks i=(bootstrapped s (loadedNode a bits tail) ra rd rc words).stacks i) ∧
--         Trace (compiled prepareNode 301 832) (ticks+1)
--           (a.withPC (some (compiled prepareNode 301 832).entry)) (b.withPC none) ∧
--         ∀ k z,k ≤ ticks+1 → Trace (compiled prepareNode 301 832) k
--           (a.withPC (some (compiled prepareNode 301 832).entry)) z →
--           ∀ i,(z.stacks i).length ≤ 896*B+20000*(B+1)^4+300*(B+1)+1
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.BitProgram.Cfg`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Trace`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.State`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.compiled`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.unary` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.PairNativeSetup.scratch`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.leafRegs` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler.Nodes.lowPort` (definitions bundle `OAIQ081S021` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Eval` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.StructuredCalls.projectState` (definitions bundle `OAIQ081S025` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighIncidenceProgram.descendingHighMask` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.CacheCorrect` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Inputs` (definitions bundle `OAIQ081S091` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage.WordBound` (definitions bundle `OAIQ081S106` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader.bootstrapOutputBound` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native.Ready` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLayoutLoad.SourceBank` (definitions bundle `OAIQ081S165` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepareNode` (definitions bundle `OAIQ081S172` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.Data` (definitions bundle `OAIQ081S175` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.bootstrapped` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.loadedNode` (definitions bundle `OAIQ081S185` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.encodeList` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_native_run` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/QueryNodeEvaluation.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation.prepare_eval)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S185

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation

open OAI BitProgram StructuredCalls SqrtLog SubexpSetupStorage
open LeafHeadSetupProgram QueryTupleState

theorem prepare_eval (s : Native.Inputs) (a : Data)
    (bits : List Bool) (tail : List (List Bool))
    (H : Finset (Fin s.n)) (J B : ℕ)
    (hsource : NativeLayoutLoad.SourceBank s a)
    (hcursor : a.stacks 301=Encoding.encodeList id (bits::tail))
    (hmask : a.stacks 338=HighIncidenceProgram.descendingHighMask H)
    (horder : a.stacks 243=List.replicate J true)
    (hb : WordBound B a) (hcap : SignatureHeadLoader.bootstrapOutputBound s ≤ B) :
    ∃ ra rd rc words ticks b,
      CacheCorrect s.height (unary s.R) s.width words ∧
      Eval prepareNode ticks a b ∧ ticks ≤ 20000*(B+1)^4+300*(B+1) ∧
      WordBound B b ∧
      Native.Ready s (projectState SignatureHeadLoader.leafRegs QueryAssembler.Nodes.lowPort b) ∧
      b.stacks 832=List.replicate (s.n-H.card) true ∧ b.stacks 833=List.replicate J true ∧
      b.stacks 834=[] ∧ b.stacks 835=[] ∧ b.stacks 850=[] ∧ b.stacks 851=[] ∧
      (∀ i ∈ PairNativeSetup.scratch,b.stacks i=[]) ∧
      (∀ i, i ∉ PairNativeSetup.scratch → i ≠ 832 → i ≠ 833 → i ≠ 834 → i ≠ 835 →
        b.stacks i=(bootstrapped s (loadedNode a bits tail) ra rd rc words).stacks i) ∧
      Trace (compiled prepareNode 301 832) (ticks+1)
        (a.withPC (some (compiled prepareNode 301 832).entry)) (b.withPC none) ∧
      ∀ k z,k ≤ ticks+1 → Trace (compiled prepareNode 301 832) k
        (a.withPC (some (compiled prepareNode 301 832).entry)) z →
        ∀ i,(z.stacks i).length ≤ 896*B+20000*(B+1)^4+300*(B+1)+1 := by
  sorry

open LeafParametersProgram LeafProgram LeafProgram.PreparedSource

open SubexpLiftRing SubexpQuarticRing
open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryNodeEvaluation
end
