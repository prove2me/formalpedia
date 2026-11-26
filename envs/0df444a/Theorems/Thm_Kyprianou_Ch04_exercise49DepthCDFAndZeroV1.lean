-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise49DepthCDFAndZeroV1
-- name    : Kyprianou.Ch04.exercise49DepthCDFAndZeroV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T16:32:27.150294+00:00
-- url     : https://prove2.me/theorems/2e0510f5-3af1-55b2-9684-be616d587fb2
-- title:
--   The rational depth distribution gives survival probabilities and vanishes on no ruin
-- statement:
--   The rational depth distribution gives survival probabilities and vanishes on no ruin
-- source:
--   Kyprianou (2006), Exercise 4.9(iii), p.109

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_9CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise49DepthCDFAndZeroV1
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
    (∀ x : ℝ, 0 ≤ x →
      P (V ⁻¹' Iic x) = P {w | (sInf {v : WithTop NNReal |
        ∃ t : NNReal, v = ↑t ∧ 0 < t ∧ x + X t w < 0}) = ⊤}) ∧
    (∀ᵐ w ∂P.restrict {w | τ w = ⊤}, V w = 0) := by
  sorry
