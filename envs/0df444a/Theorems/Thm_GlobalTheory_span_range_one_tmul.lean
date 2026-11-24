-- Prove2me | Theorems.Thm_GlobalTheory_span_range_one_tmul
-- name    : GlobalTheory.span_range_one_tmul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:21:30.445352+00:00
-- url     : https://prove2.me/theorems/1c11aed5-bd2a-4a64-ac37-7e8863de9a2d
-- title:
--   Global Theory: span range one tmul
-- statement:
--   The Global Theory construction uses the span range one tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L298-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L298-L307

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

theorem GlobalTheory.span_range_one_tmul :
    Submodule.span ℝ (Set.range fun x : X => (1 : ℝ) ⊗ₜ[ℤ] x) = ⊤ := by sorry
