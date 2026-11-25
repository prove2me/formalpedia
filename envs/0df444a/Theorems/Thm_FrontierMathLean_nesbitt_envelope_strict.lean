-- Prove2me | Theorems.Thm_FrontierMathLean_nesbitt_envelope_strict
-- name    : FrontierMathLean.nesbitt_envelope_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:36:22.273142+00:00
-- url     : https://prove2.me/theorems/6a3d8ae0-1cb0-5634-a6a5-c5cd4a5c27fb
-- title:
--   Frontier Math Lean: nesbitt envelope strict
-- statement:
--   Strict form of `nesbitt_envelope_mono` above the endpoint `2`.
--
--   Source: https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/NesbittRatioInequality.lean#L55-L73
-- source:
--   https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/NesbittRatioInequality.lean#L55-L73

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_FrontierMathLean_NesbittRatioInequality
set_option autoImplicit false
open FrontierMathLean

theorem FrontierMathLean.nesbitt_envelope_strict
    {s t : ℝ} (ht : 2 < t) (hts : t < s) :
    1 / t + 2 * t / (t + 2) < 1 / s + 2 * s / (s + 2) := by sorry
