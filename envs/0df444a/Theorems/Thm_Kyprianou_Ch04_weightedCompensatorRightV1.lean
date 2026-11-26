-- Prove2me | Theorems.Thm_Kyprianou_Ch04_weightedCompensatorRightV1
-- name    : Kyprianou.Ch04.weightedCompensatorRightV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:41:32.01238+00:00
-- url     : https://prove2.me/theorems/d1e75ee6-c424-53f0-800e-1239d867aa42
-- title:
--   Right continuity of weighted mark compensators along measurable paths
-- statement:
--   Right continuity of weighted mark compensators along measurable paths
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, auxiliary lemma.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem weightedCompensatorRightV1 (ν : Measure ℝ) (B : Set ℝ) (L : NNReal → ℝ)
    (hL : Measurable L) (f : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hc : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici 0 ×ˢ univ))
    (hb : ∀ s x : ℝ, 0 ≤ s → |f s x| ≤ K) :
    ∀ t : NNReal, Tendsto
      (fun v : NNReal => ∫ s in Icc (0 : ℝ) (v : ℝ),
        (∫ x in B, x * f s (L s.toNNReal) ∂ν) ∂volume)
      (𝓝[>] t) (𝓝 (∫ s in Icc (0 : ℝ) (t : ℝ),
        (∫ x in B, x * f s (L s.toNNReal) ∂ν) ∂volume)) := by
  sorry
end Kyprianou.Ch04
