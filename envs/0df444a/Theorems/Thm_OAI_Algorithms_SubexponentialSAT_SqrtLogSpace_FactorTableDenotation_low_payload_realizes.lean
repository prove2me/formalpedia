-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_FactorTableDenotation_low_payload_realizes
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation.low_payload_realizes
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T02:28:20.265697+00:00
-- url     : https://prove2.me/theorems/2b283b86-6ef8-4866-9773-7d8e46db3367
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation.low_payload_realizes: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation.low_payload_realizes` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableDenotation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableDenotation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation`, with `open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing`, `open MomentsProgram TruncatedRingProgram DensePolynomialProgram`, `open OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes LayoutProgram`, `open scoped BigOperators`):
--
--   ```lean
--   theorem low_payload_realizes {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
--       (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
--       (u J n f j : ℕ) (hu : 0 < u) (hJ : 0 < J)
--       (theta : Coeff (baseWidth 3 p.t) d)
--       (xs : List (Fixed.Array (baseWidth 3 p.t) d (p.R + 1)))
--       (hx : xs.length = n) (choice mask : List Bool) (hc : choice.length = n)
--       (hs : PerturbationAssembly.sourceRowProperty p ps P n f j xs) :
--       ∃ entries : List (Product.Entry n (baseWidth 3 p.t) d),
--         FactorTableNative.specializedRowPayload p.t p.model p.modulus p.cache J (p.R + 1)
--           theta (PerturbationAssembly.pairChoice xs choice) mask = Product.bytes entries ∧
--         Good ∅ u J entries ∧
--         rawDenote p.ops.decode entries =
--           specializedJet u J mask (fixedLowJet p ps P n f j theta choice)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` and `OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking.PackingData` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost.RepresentedRing` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.MulticolorTypes.UniversalType` (definitions bundle `OAIQ081S026` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.Base` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.F` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Jet` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.O` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Coeff` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.DensePolynomialProgram.Fixed.Array` (definitions bundle `OAIQ081S100` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation.specializedJet` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.bytes` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.pairChoice` (definitions bundle `OAIQ081S136` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableNative.specializedRowPayload`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.Good` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.rawDenote` (definitions bundle `OAIQ081S151` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.Parameters.ops` (definitions bundle `OAIQ081S157` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssembly.sourceRowProperty` (definitions bundle `OAIQ081S177` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation.fixedLowJet` (definitions bundle `OAIQ081S183` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.Input.payload_correct` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/FactorTableDenotation.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation.low_payload_realizes)

import Mathlib
import Definitions.Def_OAIQ081S183

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram TruncatedRingProgram DensePolynomialProgram
open OAI.Algorithms.SubexponentialSAT.Subexp.ConstructivePacking OAI.Algorithms.SubexponentialSAT.MulticolorTypes LayoutProgram
open scoped BigOperators
noncomputable section
variable {R : Type*} [CommRing R]

theorem low_payload_realizes {r Q d : ℕ} (p : SourceBank.Parameters r Q d)
    (ps : List (ℕ × ℕ)) (P : PackingData (Fin ps.length) (UniversalType r Q 1))
    (u J n f j : ℕ) (hu : 0 < u) (hJ : 0 < J)
    (theta : Coeff (baseWidth 3 p.t) d)
    (xs : List (Fixed.Array (baseWidth 3 p.t) d (p.R + 1)))
    (hx : xs.length = n) (choice mask : List Bool) (hc : choice.length = n)
    (hs : PerturbationAssembly.sourceRowProperty p ps P n f j xs) :
    ∃ entries : List (Product.Entry n (baseWidth 3 p.t) d),
      FactorTableNative.specializedRowPayload p.t p.model p.modulus p.cache J (p.R + 1)
        theta (PerturbationAssembly.pairChoice xs choice) mask = Product.bytes entries ∧
      Good ∅ u J entries ∧
      rawDenote p.ops.decode entries =
        specializedJet u J mask (fixedLowJet p ps P n f j theta choice) := by
  sorry

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorTableDenotation
end
