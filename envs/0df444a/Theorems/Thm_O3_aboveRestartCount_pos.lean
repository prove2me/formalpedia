-- Prove2me | Theorems.Thm_O3_aboveRestartCount_pos
-- name    : O3.aboveRestartCount_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:05:02.748736+00:00
-- url     : https://prove2.me/theorems/2d33bc00-8efb-4f0b-835c-25b2483be3e1
-- title:
--   O3: above Restart Count pos
-- statement:
--   The O3 construction uses the above Restart Count pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L185-L191
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L185-L191

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.aboveRestartCount_pos {Delta0 delta : ℝ}
    (hdelta : 0 < delta) (horder : delta < Delta0) :
    0 < aboveRestartCount Delta0 delta := by sorry
