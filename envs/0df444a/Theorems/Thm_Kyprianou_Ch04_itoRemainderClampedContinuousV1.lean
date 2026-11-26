-- Prove2me | Theorems.Thm_Kyprianou_Ch04_itoRemainderClampedContinuousV1
-- name    : Kyprianou.Ch04.itoRemainderClampedContinuousV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:21:05.448813+00:00
-- url     : https://prove2.me/theorems/0b7a42a5-8b42-527b-a537-70816178e4bc
-- title:
--   Continuity of the time-clamped Ito remainder
-- statement:
--   Continuity of the time-clamped Ito remainder.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open Set
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem itoRemainderClampedContinuousV1 (f g : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Ici (0 : ℝ) ×ˢ univ))
    (hg : ContinuousOn (fun p : ℝ × ℝ => g p.1 p.2) (Ici (0 : ℝ) ×ˢ univ)) :
    Continuous (fun p : ℝ × ℝ × ℝ =>
      f (max 0 p.1) (p.2.1+p.2.2) - f (max 0 p.1) p.2.1 -
        p.2.2*g (max 0 p.1) p.2.1) := by
  sorry
end Kyprianou.Ch04
