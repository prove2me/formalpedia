-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram_product_dense
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.product_dense
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:24:07.40529+00:00
-- url     : https://prove2.me/theorems/86d3a856-c923-44bf-b05a-e2b9fac65988
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.product_dense: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.product_dense` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/TruncatedRingProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/TruncatedRingProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram`, with `open scoped BigOperators`, `open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing`, `open MomentsProgram BitProgram`):
--
--   ```lean
--   theorem product_dense (p t : ℕ) [Fact p.Prime]
--       (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
--       {n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
--       (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
--       (htable : ∀ i j, basis i * basis j =
--         ∑ k, scalar (wordValue p t (table i j k)) * basis k)
--       (u J : ℕ) (left right : List (Product.Entry n (baseWidth p t) d)) :
--       let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
--       rawValue u J f (Product.run p t M cache table u J left right []) =
--         rawValue u J f left * rawValue u J f right
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instMulOfCommSemiring` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` and `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.wordValue` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.denote` (definitions bundle `OAIQ081S027` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCode` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.scalarRing` (definitions bundle `OAIQ081S082` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Dense` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Truncated.instCommSemiring` (definitions bundle `OAIQ081S115` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.run` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.rawValue` (definitions bundle `OAIQ081S151` of this split).
--
--   **Used by.** The proofs of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.hash_step_value`, `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorAssignmentCallback.marked_step_value` and `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram.multiply_run` of this split import it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/TruncatedRingProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.product_dense)

import Mathlib
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S151

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram

open scoped BigOperators
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram BitProgram

variable {V R : Type*} [DecidableEq V] [CommRing R]

noncomputable section

theorem product_dense (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (scalar : ZMod (p ^ t) →+* R) (basis : Fin d → R)
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (htable : ∀ i j, basis i * basis j =
      ∑ k, scalar (wordValue p t (table i j k)) * basis k)
    (u J : ℕ) (left right : List (Product.Entry n (baseWidth p t) d)) :
    let f := RingProgram.denote (RingProgram.scalarRing p t M cache) scalar basis
    rawValue u J f (Product.run p t M cache table u J left right []) =
      rawValue u J f left * rawValue u J f right := by
  sorry

end

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end
