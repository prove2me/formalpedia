-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashCircuitProgram_Cost_negative_le
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.negative_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:51:05.800073+00:00
-- url     : https://prove2.me/theorems/b18c6ad4-8bc6-4a6e-b599-5bcbcc982116
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.negative_le: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.negative_le` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramCost.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramCost.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost`, with `open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing`, `open MomentsProgram`, `open Native`, `open LeafProgram.NativeSemantics`):
--
--   ```lean
--   theorem negative_le (a : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J a) :
--       LiteralCallback.negateBudget p t M cache table minusOne one a degree ≤
--         negativeBound (baseWidth p t) d n u J S
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.Code` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.negativeBound` (definitions bundle `OAIQ081S008` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.Squarefree.Sparse.supportUniverse` (definitions bundle `OAIQ081S009` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.LiteralCallback.negateBudget` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.NativeSemantics.Good` (definitions bundle `OAIQ081S144` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.literal_le` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/HashCircuitProgramCost.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost.negative_le)

import Mathlib
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S144

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram
open Native
open LeafProgram.NativeSemantics

variable {n B d u J S : ℕ} {vars : Finset (Fin n)}

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t)
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (hS : u*J*(Squarefree.Sparse.supportUniverse vars J).card ≤ S)

variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (hone : Good vars u J one) (hi : ∀ v, Good vars u J (incidence v))
variable (degree : List Bool) (hd : degree.length = d)

include hS hone hd in
theorem negative_le (a : List (Product.Entry n (baseWidth p t) d)) (ha : Good vars u J a) :
    LiteralCallback.negateBudget p t M cache table minusOne one a degree ≤
      negativeBound (baseWidth p t) d n u J S := by
  sorry

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Cost

end OAI.Algorithms
end
