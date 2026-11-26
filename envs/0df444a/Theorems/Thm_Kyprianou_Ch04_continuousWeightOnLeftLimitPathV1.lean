-- Prove2me | Theorems.Thm_Kyprianou_Ch04_continuousWeightOnLeftLimitPathV1
-- name    : Kyprianou.Ch04.continuousWeightOnLeftLimitPathV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:43:31.220852+00:00
-- url     : https://prove2.me/theorems/4f939b89-7584-4b18-b503-d2e0a1cb7d57
-- title:
--   Strict-left continuous weights of a left-limit path
-- statement:
--   The supplied positive-time left limits agree with the canonical left limit, which is continuous from the left. Compose with the joint continuous time-space function.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(i).

import Mathlib
open Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem continuousWeightOnLeftLimitPathV1 (Y L : NNReal → ℝ) (f : ℝ → ℝ → ℝ)
    (hL : ∀ t, 0 < t → Tendsto Y (𝓝[<] t) (𝓝 (L t)))
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ)) :
    ∀ r, 0 < r → Tendsto (fun t : NNReal => f (t : ℝ) (L t))
      (𝓝[<] r) (𝓝 (f (r : ℝ) (L r))) := by
  sorry
end Kyprianou.Ch04
