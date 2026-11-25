-- Prove2me | Theorems.Thm_FrontierMathLean_nesbitt_envelope_mono
-- name    : FrontierMathLean.nesbitt_envelope_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:36:27.095361+00:00
-- url     : https://prove2.me/theorems/50eb186a-ddbd-42e6-bbf3-7e267b309719
-- title:
--   Frontier Math Lean: nesbitt envelope mono
-- statement:
--   The one-variable lower envelope is increasing from the point corresponding
--   to ratio one.
--
--   Source: https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/NesbittRatioInequality.lean#L34-L52
-- source:
--   https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/FrontierMathLean/NesbittRatioInequality.lean#L34-L52

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_FrontierMathLean_NesbittRatioInequality
set_option autoImplicit false
open FrontierMathLean

theorem FrontierMathLean.nesbitt_envelope_mono
    {s t : ℝ} (ht : 2 ≤ t) (hts : t ≤ s) :
    1 / t + 2 * t / (t + 2) ≤ 1 / s + 2 * s / (s + 2) := by sorry
