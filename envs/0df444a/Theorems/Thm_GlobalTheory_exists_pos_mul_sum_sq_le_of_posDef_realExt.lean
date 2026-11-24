-- Prove2me | Theorems.Thm_GlobalTheory_exists_pos_mul_sum_sq_le_of_posDef_realExt
-- name    : GlobalTheory.exists_pos_mul_sum_sq_le_of_posDef_realExt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:36:14.699468+00:00
-- url     : https://prove2.me/theorems/6071aa52-ceca-4b8a-a086-6f59d7347429
-- title:
--   Global Theory: exists pos mul sum sq le of pos Def real Ext
-- statement:
--   The Global Theory construction uses the exists pos mul sum sq le of pos Def real Ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L320-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L320-L331

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X : Type*} [AddCommGroup X]

theorem GlobalTheory.exists_pos_mul_sum_sq_le_of_posDef_realExt {ι : Type*} [Fintype ι] (b : Basis ι ℤ X)
    {Q : QuadraticMap ℤ X ℝ} (hQ : (realExt Q).PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ x, c * ∑ i, (b.repr x i : ℝ) ^ 2 ≤ Q x := by sorry
