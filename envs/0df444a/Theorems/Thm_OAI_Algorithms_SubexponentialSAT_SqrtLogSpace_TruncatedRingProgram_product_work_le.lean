-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram_product_work_le
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.product_work_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T01:24:05.042974+00:00
-- url     : https://prove2.me/theorems/f4d231ce-2264-4bc9-be02-48e6f0a34f5e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.product_work_le: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.product_work_le` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/TruncatedRingProgram.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/TruncatedRingProgram.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram`, with `open scoped BigOperators`, `open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing`, `open MomentsProgram BitProgram`):
--
--   ```lean
--   theorem product_work_le (p t : ℕ) [Fact p.Prime]
--       (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
--       {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
--       (u J : ℕ) (left right : List (Product.Entry n (baseWidth p t) d))
--       (hl : Good ∅ u J left) (hr : Good ∅ u J right) :
--       Product.work p t M cache table u J left right [] + 2 ≤
--         productBudget n (baseWidth p t) d u J
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing.Word` (definitions bundle `OAIQ081S001` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpLiftRing.baseWidth` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpPreparedQuartic.Modulus` (definitions bundle `OAIQ081S024` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.productBudget` (definitions bundle `OAIQ081S043` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgram.ScalarCache` (definitions bundle `OAIQ081S048` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.Entry` (definitions bundle `OAIQ081S118` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.MomentsProgram.Product.work` (definitions bundle `OAIQ081S139` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.Good` (definitions bundle `OAIQ081S151` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FactorProductSpace.accumulate_run_space` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/TruncatedRingProgram.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram.product_work_le)

import Mathlib
import Definitions.Def_OAIQ081S139
import Definitions.Def_OAIQ081S151

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram

open scoped BigOperators
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram BitProgram

variable {V R : Type*} [DecidableEq V] [CommRing R]

theorem product_work_le (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    {n d : ℕ} (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (u J : ℕ) (left right : List (Product.Entry n (baseWidth p t) d))
    (hl : Good ∅ u J left) (hr : Good ∅ u J right) :
    Product.work p t M cache table u J left right [] + 2 ≤
      productBudget n (baseWidth p t) d u J := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end
