-- Prove2me | Theorems.Thm_O3_two_rpow_gt_one
-- name    : O3.two_rpow_gt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:24:28.824255+00:00
-- url     : https://prove2.me/theorems/1be6680d-a67e-4f46-82d4-dd0dec58ce0c
-- title:
--   O3: two rpow gt one
-- statement:
--   The O3 construction uses the two rpow gt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage11Amortization.lean#L37-L39
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage11Amortization.lean#L37-L39

import Definitions.Def_O3_AboveTwo
import Definitions.Def_O3_Stage11Amortization
set_option autoImplicit true
open O3

theorem O3.two_rpow_gt_one {a : ℝ} (ha : 0 < a) :
    1 < (2 : ℝ) ^ a := by sorry
