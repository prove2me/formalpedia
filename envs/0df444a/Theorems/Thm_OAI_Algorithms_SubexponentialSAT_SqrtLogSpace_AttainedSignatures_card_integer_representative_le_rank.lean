-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_AttainedSignatures_card_integer_representative_le_rank
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures.card_integer_representative_le_rank
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:13:33.30799+00:00
-- url     : https://prove2.me/theorems/13606497-066c-4a9b-bdeb-a4ab6f45f42e
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures.card_integer_representative_le_rank: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures.card_integer_representative_le_rank` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/AttainedSignatures.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/AttainedSignatures.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures`):
--
--   ```lean
--   theorem card_integer_representative_le_rank {d h : ℕ} (A : Fin d → Fin h → ℤ)
--       (W : ℕ) (hA : ∀ j i, |A j i| ≤ (W : ℤ)) :
--       Nat.card (Representative (integerKey A)) ≤
--         (2 * h * W + 1) ^ OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank.rowRank A
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank.rowRank` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures.Representative` (definitions bundle `OAIQ081S020` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures.integerKey` (definitions bundle `OAIQ081S114` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets.actual_key_inventory_le_maxRank` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/AttainedSignatures.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures.card_integer_representative_le_rank)

import Mathlib
import Definitions.Def_OAIQ081S114

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures

variable {N : ℕ} {κ : Type*} (key : Fin N → κ)

theorem card_integer_representative_le_rank {d h : ℕ} (A : Fin d → Fin h → ℤ)
    (W : ℕ) (hA : ∀ j i, |A j i| ≤ (W : ℤ)) :
    Nat.card (Representative (integerKey A)) ≤
      (2 * h * W + 1) ^ OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutRank.rowRank A := by
  sorry

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures
end
