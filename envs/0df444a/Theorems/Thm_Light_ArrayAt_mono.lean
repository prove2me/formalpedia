-- Prove2me | Theorems.Thm_Light_ArrayAt_mono
-- name    : Light.ArrayAt.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:03:12.303221+00:00
-- url     : https://prove2.me/theorems/8f7e48e3-1a04-4998-a6a1-8cd08e6ffbce
-- title:
--   Array At: mono
-- statement:
--   The bound `U` on the entries and the address `top` may grow.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L87-L89
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L87-L89

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
import Theorems.Thm_Light_Ends_mono
import Theorems.Thm_Light_SameOn_mono
import Theorems.Thm_Light_SameOutside_mono
set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
open Light.ArrayAt

theorem Light.ArrayAt.mono (h : ArrayAt μ a l N U top)
    (hU : U ≤ U' := by
      first
      | omega
      | ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
    (ht : top ≤ top' := by
      first
      | omega
      | ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)) :
    ArrayAt μ a l N U' top' := by sorry
