-- Prove2me | Theorems.Thm_Kyprianou_Ch04_leftLimitSquareSupV1
-- name    : Kyprianou.Ch04.leftLimitSquareSupV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:46:14.4678+00:00
-- url     : https://prove2.me/theorems/34b4bb52-5b49-5822-b293-74823a0340aa
-- title:
--   Positive-time left-limit difference inherits compact square bound
-- statement:
--   Positive-time left-limit difference inherits compact square bound
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem leftLimitSquareSupV1 (U V : NNReal → ℝ) (u v : ℝ) (t T : NNReal)
    (ht : 0 < t) (hT : t ≤ T)
    (hu : Tendsto U (𝓝[<] t) (𝓝 u))
    (hv : Tendsto V (𝓝[<] t) (𝓝 v))
    (hb : BddAbove ((fun s : NNReal => |U s - V s|^2) '' Iic T)) :
    (u - v)^2 ≤ sSup ((fun s : NNReal => |U s - V s|^2) '' Iic T) := by
  sorry
end Kyprianou.Ch04
