-- Prove2me | Theorems.Thm_O3_aboveMu_pos
-- name    : O3.aboveMu_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:04:04.979964+00:00
-- url     : https://prove2.me/theorems/e221e54c-df45-5651-8d00-af8065d95ea0
-- title:
--   O3: above Mu pos
-- statement:
--   The O3 construction uses the above Mu pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L137-L141
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/AboveTwo.lean#L137-L141

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_AboveTwo
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.aboveMu_pos {p eps D : ℝ}
    (_hp : AboveTwoRegime p) (heps : 0 < eps) (hD : 0 < D) :
    0 < aboveMu p eps D := by sorry
