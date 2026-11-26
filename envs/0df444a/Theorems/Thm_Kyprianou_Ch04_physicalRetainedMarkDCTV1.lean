-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalRetainedMarkDCTV1
-- name    : Kyprianou.Ch04.physicalRetainedMarkDCTV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T17:20:32.358962+00:00
-- url     : https://prove2.me/theorems/1b30a755-fdd2-5ce0-a05e-1d19277b147b
-- title:
--   Retained mark convergence with a common integrable envelope
-- statement:
--   Retained mark convergence with a common integrable envelope.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5(iii).

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem physicalRetainedMarkDCTV1 (R : Measure (ℝ × ℝ)) (T : NNReal)
    (J : ℕ → ℝ × ℝ → ℝ) (G : ℝ × ℝ → ℝ)
    (e : ℕ → ℝ) (B : ℝ × ℝ → ℝ)
    (he : Tendsto e atTop (𝓝 0))
    (hJ : ∀ n, Measurable (J n))
    (hB : IntegrableOn B (Icc (0 : ℝ) (T : ℝ) ×ˢ univ) R)
    (hdom : ∀ n z, z ∈ Icc (0 : ℝ) (T : ℝ) ×ˢ univ → |J n z| ≤ B z)
    (hz : ∀ n s, J n (s,0) = 0) (hGz : ∀ s, G (s,0) = 0)
    (hconv : ∀ᵐ z ∂ R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ univ),
      z.2 ≠ 0 → Tendsto (fun n => J n z) atTop (𝓝 (G z))) :
    Tendsto (fun n => ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e n < |x|}, J n z ∂ R)
      atTop (𝓝 (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ univ, G z ∂ R)) := by
  sorry
end Kyprianou.Ch04
