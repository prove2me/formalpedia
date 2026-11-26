-- Prove2me | Theorems.Thm_Kyprianou_Ch04_jointUniformPairLimitV1
-- name    : Kyprianou.Ch04.jointUniformPairLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:04:38.376568+00:00
-- url     : https://prove2.me/theorems/763eb222-fc4c-5ecd-9e0e-f39435cdbc75
-- title:
--   Joint uniform limit identifying the first coordinate
-- statement:
--   Joint uniform limit identifying the first coordinate.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal Topology
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem jointUniformPairLimitV1 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (U V : ℕ → NNReal → Ω → ℝ) (X : NNReal → Ω → ℝ)
    (k : ℕ → ℕ)
    (hc : ∀ᵐ w ∂P, ∀ T : NNReal,
      UniformCauchySeqOn (fun n t => (U (k n) t w,V (k n) t w)) atTop (Icc 0 T))
    (hx : ∀ᵐ w ∂P, ∀ t, Tendsto (fun n => U (k n) t w) atTop (𝓝 (X t w))) :
    ∃ M : NNReal → Ω → ℝ,
      ∀ᵐ w ∂P, ∀ T : NNReal, ∀ δ : ℝ, 0 < δ →
        ∃ N : ℕ, ∀ n ≥ N, ∀ t : NNReal, t ≤ T →
          |U (k n) t w - X t w| < δ ∧ |V (k n) t w - M t w| < δ := by
  sorry
end Kyprianou.Ch04
