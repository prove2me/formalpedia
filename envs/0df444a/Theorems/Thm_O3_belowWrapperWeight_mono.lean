-- Prove2me | Theorems.Thm_O3_belowWrapperWeight_mono
-- name    : O3.belowWrapperWeight_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:24:31.214646+00:00
-- url     : https://prove2.me/theorems/e480ca69-1b3e-4d39-9b03-56139b722502
-- title:
--   O3: below Wrapper Weight mono
-- statement:
--   The O3 construction uses the below Wrapper Weight mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage11Amortization.lean#L125-L141
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage11Amortization.lean#L125-L141

import Definitions.Def_O3_AboveTwo
import Definitions.Def_O3_Stage11Amortization
set_option autoImplicit true
open O3

theorem O3.belowWrapperWeight_mono :
    MonotoneOn belowWrapperWeight (Set.Ici 0) := by sorry
