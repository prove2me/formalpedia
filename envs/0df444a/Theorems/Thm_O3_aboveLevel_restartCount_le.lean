-- Prove2me | Theorems.Thm_O3_aboveLevel_restartCount_le
-- name    : O3.aboveLevel_restartCount_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:05:10.88387+00:00
-- url     : https://prove2.me/theorems/afe7c6ae-69a5-460e-9c6f-3fa46eb3389b
-- title:
--   O3: above Level restart Count le
-- statement:
--   The ceiling-defined restart count reaches the terminal level.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L204-L223
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L204-L223

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.aboveLevel_restartCount_le {Delta0 delta : ℝ}
    (hDelta0 : 0 < Delta0) (hdelta : 0 < delta) :
    aboveLevel Delta0 (aboveRestartCount Delta0 delta) ≤ delta := by sorry
