-- Prove2me | Theorems.Thm_Light_ListAt_mono
-- name    : Light.ListAt.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:03:13.201815+00:00
-- url     : https://prove2.me/theorems/e579848e-5ac5-4a62-99de-34083be776a7
-- title:
--   List At: mono
-- statement:
--   The address `top` may grow.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L59-L60
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/ArrayAt.lean#L59-L60

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
open Light.ListAt

theorem Light.ListAt.mono (h : ListAt μ a l N top)
    (ht : top ≤ top' := by
      first
      | omega
      | ( (try have := _root_.Light.Std.space_le (by assumption))
          (try have := _root_.Light.Std.const_le (by assumption))
          simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)) :
    ListAt μ a l N top' := by sorry
