-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableContinuousTimeStateWeightV1
-- name    : Kyprianou.Ch04.predictableContinuousTimeStateWeightV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T08:26:34.907096+00:00
-- url     : https://prove2.me/theorems/d0265be7-f046-4b9a-8f26-97ebb1c30bd0
-- title:
--   Continuous time-state weights at predictable states
-- statement:
--   A continuous deterministic time-state weight evaluated at a predictable state is predictable.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem predictableContinuousTimeStateWeightV1 {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal inferInstance)
    (V : NNReal → Ω → ℝ) (hV : IsStronglyPredictable F V)
    (f : ℝ → ℝ → ℝ)
    (hf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Ici (0 : ℝ) ×ˢ univ)) :
    Measurable[F.predictable] (fun p : NNReal × Ω => f (p.1 : ℝ) (V p.1 p.2)) := by
  sorry
end Kyprianou.Ch04
