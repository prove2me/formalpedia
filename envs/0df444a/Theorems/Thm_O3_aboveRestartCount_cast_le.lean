-- Prove2me | Theorems.Thm_O3_aboveRestartCount_cast_le
-- name    : O3.aboveRestartCount_cast_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:04:42.134139+00:00
-- url     : https://prove2.me/theorems/0855d0cd-c45a-521c-a60e-172b74672bfa
-- title:
--   O3: above Restart Count cast le
-- statement:
--   Exact logarithmic ceiling bound; no `Delta_0/delta` overhead appears.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L194-L201
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L194-L201

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.aboveRestartCount_cast_le {Delta0 delta : ℝ}
    (hdelta : 0 < delta) (horder : delta ≤ Delta0) :
    (aboveRestartCount Delta0 delta : ℝ) ≤
      Real.logb 2 (Delta0 / delta) + 1 := by sorry
