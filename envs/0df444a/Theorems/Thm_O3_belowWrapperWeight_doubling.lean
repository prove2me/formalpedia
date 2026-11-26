-- Prove2me | Theorems.Thm_O3_belowWrapperWeight_doubling
-- name    : O3.belowWrapperWeight_doubling
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:27:55.135082+00:00
-- url     : https://prove2.me/theorems/a478b586-4ebe-5c28-94d3-50db981bd55f
-- title:
--   O3: below Wrapper Weight doubling
-- statement:
--   The O3 construction uses the below Wrapper Weight doubling property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage11Amortization.lean#L143-L159
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage11Amortization.lean#L143-L159

import Definitions.Def_O3_AboveTwo
import Definitions.Def_O3_Stage11Amortization
set_option autoImplicit true
open O3

theorem O3.belowWrapperWeight_doubling :
    DoublingWeight belowWrapperWeight (Real.sqrt 2) := by sorry
