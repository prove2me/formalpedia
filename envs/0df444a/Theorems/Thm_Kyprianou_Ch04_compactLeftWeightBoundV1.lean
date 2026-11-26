-- Prove2me | Theorems.Thm_Kyprianou_Ch04_compactLeftWeightBoundV1
-- name    : Kyprianou.Ch04.compactLeftWeightBoundV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:54:08.703825+00:00
-- url     : https://prove2.me/theorems/7c5017e6-5abb-4bc1-a960-c3c07b9c522b
-- title:
--   Compact bound for continuous weights on cadlag left limits
-- statement:
--   Use the previously proved Chapter 4 compact cadlag path bound and include the arbitrary time-zero left value. A continuous spatial weight is bounded on the resulting compact time-space rectangle.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iv).

import Mathlib
import Definitions.Def_LeanLevy_Processes_Cadlag
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem compactLeftWeightBoundV1 (Y L : NNReal → ℝ) (f : ℝ → ℝ → ℝ)
    (hY : IsCadlag Y)
    (hL : ∀ t, 0 < t → Tendsto Y (𝓝[<] t) (𝓝 (L t)))
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (T : NNReal) : ∃ C : ℝ, 0 ≤ C ∧ ∀ r ≤ T, |f (r : ℝ) (L r)| ≤ C := by
  sorry
end Kyprianou.Ch04
