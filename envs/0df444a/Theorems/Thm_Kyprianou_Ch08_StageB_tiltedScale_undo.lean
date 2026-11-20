-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_tiltedScale_undo
-- name    : Kyprianou.Ch08.StageB.tiltedScale_undo
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:43:02.860111+00:00
-- url     : https://prove2.me/theorems/96b3620e-211e-4edd-814e-5d15c0590fe7
-- title:
--   Chapter 8 exponential untwisting of Esscher-tilted scale functions
-- statement:
--   Exponential untwisting identity for the Esscher scale transform: e^(cx) [e^(-cx)W(x)] = W(x). The deterministic algebraic ingredient in Chapter 8 Lemma 8.4 and the scale-family change of measure.
-- source:
--   Kyprianou (2006), Chapter 8, (8.19) and Lemma 8.4 equation (8.25), printed pp. 220 and 222.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_A
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB

/-- Exponential tilt of a scale function cancels against its inverse tilt. -/
theorem tiltedScale_undo (c x : ℝ) (W : ℝ → ℝ) :
    Real.exp (c * x) * tiltedScale c W x = W x := by
  sorry

end Kyprianou.Ch08.StageB
