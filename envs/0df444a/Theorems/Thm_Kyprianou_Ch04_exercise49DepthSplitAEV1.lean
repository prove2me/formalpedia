-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49DepthSplitAEV1
-- name    : Kyprianou.Ch04.exercise49DepthSplitAEV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:32:31.602286+00:00
-- url     : https://prove2.me/theorems/1df78df3-049f-578b-a44c-db3e0dc605fa
-- title:
--   The finite-passage deficit plus future depth equals the original all-time depth almost surely
-- statement:
--   The finite-passage deficit plus future depth equals the original all-time depth almost surely
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49DepthSplitAEV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (hm : ∀ t, Measurable (X t)) (hc : ∀ w, IsCadlag (fun t => X t w))
    (hInf : ∀ᵐ w ∂P, Tendsto (fun t : NNReal => X t w) atTop atTop)
    (τ : Ω → WithTop NNReal)
    (hτ : ∀ w, τ w = sInf {v : WithTop NNReal |
      ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ X t w < 0})
    (hτm : Measurable τ) (f : Ω → NNReal) (hf : Measurable f)
    (he : ∀ w, τ w ≠ ⊤ → τ w = (f w : WithTop NNReal)) :
    let V : Ω → ℝ := fun w => (⨆ q : ℚ, ENNReal.ofReal (-X (Real.toNNReal q) w)).toReal
    let W : Ω → ℝ := fun w => (⨆ q : ℚ,
      ENNReal.ofReal (-(X (f w + Real.toNNReal q) w - X (f w) w))).toReal
    ∀ᵐ w ∂P.restrict {w | τ w ≠ ⊤}, V w = -X (f w) w + W w := by
  sorry
