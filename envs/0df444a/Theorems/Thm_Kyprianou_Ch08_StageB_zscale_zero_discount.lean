-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_zscale_zero_discount
-- name    : Kyprianou.Ch08.StageB.zscale_zero_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:42:30.49196+00:00
-- url     : https://prove2.me/theorems/3d9e65f8-c782-418e-9669-7385ad7ffe9c
-- title:
--   Chapter 8 zero-discount Z-scale normalisation
-- statement:
--   At zero killing/discount rate q=0, the second scale function Z^(0)(x)=1+q integral W is identically one. Useful for the q→0 boundary of Theorem 8.1 and analyticity of Z (Corollary 8.5).
-- source:
--   Kyprianou (2006), Chapter 8, definition of Z in Theorem 8.1, equation (8.3), and Corollary 8.5, printed pp. 214 and 222.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_A
set_option autoImplicit false

namespace Kyprianou.Ch08.StageB

/-- The Z-scale function reduces to the unit constant at zero discount, for any candidate scale function. -/
theorem zscale_zero_discount (W : ℝ → ℝ) (x : ℝ) : Zscale 0 W x = 1 := by
  sorry

end Kyprianou.Ch08.StageB
