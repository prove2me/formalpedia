-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_NativeSemantics_row_fold_denote_scoped
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.row_fold_denote_scoped
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T01:29:32.860365+00:00
-- url     : https://prove2.me/theorems/065f0bcc-657e-4025-a4e7-71f1e4df240a
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.row_fold_denote_scoped: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.row_fold_denote_scoped` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramNativeSemantics.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramNativeSemantics.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics`, with `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`, `open MomentsProgram`, `open HashCircuitProgram`, `open HashCircuitProgram.Native`, `open scoped BigOperators`):
--
--   ```lean
--   theorem row_fold_denote_scoped (ws : List (Row.WeightedClause n (baseWidth p t) d))
--       (hs : ∀ w ∈ ws, ∀ l ∈ w.literals,
--         D (incidence l.variable) = Squarefree.canonical u J (jet l.variable))
--       (acc : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J acc) :
--       D (DynamicFold.value (Row.value p t M cache table minusOne one incidence u J) ws acc) =
--         rowFoldValue (squarefreeAlgebra u J) (fun c => Squarefree.canonical u J (scalarJet c))
--           (fun v => Squarefree.canonical u J (jet v)) (sourceTerms f ws) (D acc)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Support` (definitions bundle `OAIQ081S007` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.DynamicFold.value` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` and `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.wordValue` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.denote` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Jet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Poly`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.ZJet`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.canonical` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.instCommMonoidSupportOfDecidableEq` (definitions bundle `OAIQ081S030` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.scalarJet` (definitions bundle `OAIQ081S059` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.squarefreeAlgebra` (definitions bundle `OAIQ081S060` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.rowFoldValue` (definitions bundle `OAIQ081S077` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.scalarRing` (definitions bundle `OAIQ081S082` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.WeightedClause` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.value` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.Good` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.rawDenote` (definitions bundle `OAIQ081S144` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.sourceTerms` (definitions bundle `OAIQ081S158` of this split); `OAI.Algorithms.SubexponentialSAT.SAT.Literal` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.row_denote_scoped` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LeafProgramNativeSemantics.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.row_fold_denote_scoped)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S158

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open HashCircuitProgram
open HashCircuitProgram.Native
open scoped BigOperators

variable {R : Type*} [CommRing R]
variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (scalar : ZMod (p^t) →+* R) (basis : Fin d → R)
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (htable : ∀ i j, basis i * basis j =
  ∑ k, scalar (wordValue p t (table i j k)) * basis k)
local notation "f" => RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
local notation "D" => rawDenote (n := n) f

variable (vars : Finset (Fin n)) (u J : ℕ)
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (hone : Good vars u J one) (hi : ∀ v, Good vars u J (incidence v))
variable (hminus : RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis minusOne = -1)
variable (honeval : rawDenote (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) one =
  Squarefree.canonical u J 1)

variable (jet : Fin n → Squarefree.Jet (Fin n) R)
variable (hjet : ∀ v,
  rawDenote (RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis) (incidence v) =
    Squarefree.canonical u J (jet v))

include htable hone hi hminus honeval in
theorem row_fold_denote_scoped (ws : List (Row.WeightedClause n (baseWidth p t) d))
    (hs : ∀ w ∈ ws, ∀ l ∈ w.literals,
      D (incidence l.variable) = Squarefree.canonical u J (jet l.variable))
    (acc : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J acc) :
    D (DynamicFold.value (Row.value p t M cache table minusOne one incidence u J) ws acc) =
      rowFoldValue (squarefreeAlgebra u J) (fun c => Squarefree.canonical u J (scalarJet c))
        (fun v => Squarefree.canonical u J (jet v)) (sourceTerms f ws) (D acc) := by
  sorry

end SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics

end OAI.Algorithms
end
