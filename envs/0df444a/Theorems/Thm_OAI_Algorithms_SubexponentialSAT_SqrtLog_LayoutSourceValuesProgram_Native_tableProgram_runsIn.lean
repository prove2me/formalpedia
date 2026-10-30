-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutSourceValuesProgram_Native_tableProgram_runsIn
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.tableProgram_runsIn
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T02:47:17.756907+00:00
-- url     : https://prove2.me/theorems/5affbee9-5f5d-4b52-8734-07f5dff0e7a6
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.tableProgram_runsIn: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.tableProgram_runsIn` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceValuesProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceValuesProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native`, with `open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl`, `open MulticolorTypes IntegerRingLiftProgram`, `open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram (WordPair pairValue pairLength)`, `open scoped BigOperators`):
--
--   ```lean
--   theorem tableProgram_runsIn {r Q d : ℕ} (Hwords : List (List Bool)) (width : List Bool)
--       (power : WordPair) (as : List Bool) (R : ℕ) (start : Fin Q)
--       (u y : UniversalType r Q 1)
--       (hlen : Hwords.length = R) (hwords : ∀ x ∈ Hwords, x.length = width.length)
--       (hvalues : Hwords.map BinaryArithmetic.toNat =
--         (List.range R).map (LayoutCoefficientRecurrence.H as.length))
--       (hp : pairValue power = (2:ℤ)^(R-1))
--       (hpt : LayoutProgramScalar.wordTotal power = 2^(R-1))
--       (hwidth : Q+1 ≤ width.length) (hAQ : as.length ≤ Q) (hQ : 1 ≤ Q)
--       (t : ℕ) (ht : 0 < t) (hd : 0 < d) (a : RingModel.Data d)
--       (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
--       (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
--       (zero one minusOne invDenom : ModelCode t d)
--       (hzero : (RingProgram.modelRing t ht hd a M cache).decode zero = 0)
--       (hone : (RingProgram.modelRing t ht hd a M cache).decode one = 1)
--       (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
--       (base : Store) (ready : CachedReady t a M cache zero one minusOne base)
--       (hinv : base 252 = RingProgram.flat invDenom)
--       (hinput : ∀ i, base (numeratorPorts i) =
--         (LayoutProgram.Numerator.state
--           (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R as)
--           (fun _ => false) start u y [] [] ([],[])).stacks i)
--       (hq : (base 22).length = Q) (h37 : base 37 = [])
--       (h64 : base 64 = []) (h65 : base 65 = []) (h67 : base 67 = [])
--       (regs : Fin 16 → Bool) :
--       ∃ (words : List (List Bool)) (rf : Fin 16 → Bool),
--         words.length = Q ∧ (∀ word ∈ words, word.length = d * SubexpLiftRing.baseWidth 3 t) ∧
--         List.Forall₂ (ValidWord as.length R t ht hd a M cache invDenom u y) (List.range' 0 Q) words ∧
--         RunsIn tableProgram (tableBudget as.length R width.length (pairLength power) t d u y)
--           ((⟨regs,base⟩ : Data).withPC (some tableProgram.entry))
--           ((⟨rf,Function.update base 67 words.flatten⟩ : Data).withPC none)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.WordPair` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store` and `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence.H` (definitions bundle `OAIQ081S011` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.numeratorPorts` (definitions bundle `OAIQ081S013` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairValue` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairLength` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.flat` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.wordTotal` (definitions bundle `OAIQ081S057` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.tableBudget` (definitions bundle `OAIQ081S090` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.modelRing` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.ModelCode` (definitions bundle `OAIQ081S120` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.command` (definitions bundle `OAIQ081S125` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.IntegerRingLiftProgram.CachedReady` (definitions bundle `OAIQ081S140` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.ValidWord` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.Numerator.state` (definitions bundle `OAIQ081S156` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.unsignedSaved` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.callback` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.tableProgram` (definitions bundle `OAIQ081S186` of this split); `OAI.Algorithms.SubexponentialSAT.BinaryArithmetic.toNat` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.native_universal_cleanup_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutSourceValuesProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram.Native.tableProgram_runsIn)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S186

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

open SubexponentialSAT BitProgram StructuredCalls SubexpConvolutionControl
open MulticolorTypes IntegerRingLiftProgram
open _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram (WordPair pairValue pairLength)
open scoped BigOperators
attribute [local simp] Fin.coe_ofNat_eq_mod

namespace Native

theorem tableProgram_runsIn {r Q d : ℕ} (Hwords : List (List Bool)) (width : List Bool)
    (power : WordPair) (as : List Bool) (R : ℕ) (start : Fin Q)
    (u y : UniversalType r Q 1)
    (hlen : Hwords.length = R) (hwords : ∀ x ∈ Hwords, x.length = width.length)
    (hvalues : Hwords.map BinaryArithmetic.toNat =
      (List.range R).map (LayoutCoefficientRecurrence.H as.length))
    (hp : pairValue power = (2:ℤ)^(R-1))
    (hpt : LayoutProgramScalar.wordTotal power = 2^(R-1))
    (hwidth : Q+1 ≤ width.length) (hAQ : as.length ≤ Q) (hQ : 1 ≤ Q)
    (t : ℕ) (ht : 0 < t) (hd : 0 < d) (a : RingModel.Data d)
    (M : SubexpPreparedQuartic.Modulus 3 t) (cache : RingProgram.ScalarCache 3 t)
    (hz : BinaryArithmetic.toNat cache.zero.val < 3^t)
    (zero one minusOne invDenom : ModelCode t d)
    (hzero : (RingProgram.modelRing t ht hd a M cache).decode zero = 0)
    (hone : (RingProgram.modelRing t ht hd a M cache).decode one = 1)
    (hminus : (RingProgram.modelRing t ht hd a M cache).decode minusOne = -1)
    (base : Store) (ready : CachedReady t a M cache zero one minusOne base)
    (hinv : base 252 = RingProgram.flat invDenom)
    (hinput : ∀ i, base (numeratorPorts i) =
      (LayoutProgram.Numerator.state
        (LayoutProgramScalar.FromCounts.unsignedSaved Hwords width power R as)
        (fun _ => false) start u y [] [] ([],[])).stacks i)
    (hq : (base 22).length = Q) (h37 : base 37 = [])
    (h64 : base 64 = []) (h65 : base 65 = []) (h67 : base 67 = [])
    (regs : Fin 16 → Bool) :
    ∃ (words : List (List Bool)) (rf : Fin 16 → Bool),
      words.length = Q ∧ (∀ word ∈ words, word.length = d * SubexpLiftRing.baseWidth 3 t) ∧
      List.Forall₂ (ValidWord as.length R t ht hd a M cache invDenom u y) (List.range' 0 Q) words ∧
      RunsIn tableProgram (tableBudget as.length R width.length (pairLength power) t d u y)
        ((⟨regs,base⟩ : Data).withPC (some tableProgram.entry))
        ((⟨rf,Function.update base 67 words.flatten⟩ : Data).withPC none) := by
  sorry

end Native
end SubexponentialSAT.SqrtLog.LayoutSourceValuesProgram

end OAI.Algorithms
end
