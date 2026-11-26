-- Prove2me | Theorems.Thm_O3_aboveWrapperWeight_doubling
-- name    : O3.aboveWrapperWeight_doubling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:27:51.761978+00:00
-- url     : https://prove2.me/theorems/cf902904-474f-4aef-b587-3ca4f5af6411
-- title:
--   O3: above Wrapper Weight doubling
-- statement:
--   The O3 construction uses the above Wrapper Weight doubling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage11Amortization.lean#L107-L116
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage11Amortization.lean#L107-L116

import Definitions.Def_O3_AboveTwo
import Definitions.Def_O3_Stage11Amortization
set_option autoImplicit true
open O3

theorem O3.aboveWrapperWeight_doubling {a : ℝ} (ha : 0 < a) :
    DoublingWeight (aboveWrapperWeight a) ((2 : ℝ) ^ a) := by sorry
