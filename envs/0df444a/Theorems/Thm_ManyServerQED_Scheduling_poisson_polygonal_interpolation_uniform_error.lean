-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_poisson_polygonal_interpolation_uniform_error
-- name    : ManyServerQED.Scheduling.poisson_polygonal_interpolation_uniform_error
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T01:06:01.720355+00:00
-- url     : https://prove2.me/theorems/f2b705d1-9fb8-5d55-936a-04aca323b37b
-- title:
--   Uniform approximation of a centered Poisson process by its integer-grid interpolation
-- statement:
--   Let $N$ be a rate-one Poisson counting process. Assume its unit increments are identically distributed and have finite second moment. Centered and scaled by the square root of $n$, its actual counts and the polygonal interpolation through centered integer-grid counts are uniformly within any fixed positive tolerance on the rescaled unit interval with probability tending to one.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_DurrettProbability_Donsker
open Set MeasureTheory Filter Topology Finset DurrettProbability ProbabilityTheory
open scoped ENNReal

theorem ManyServerQED.Scheduling.poisson_polygonal_interpolation_uniform_error {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N : Ω → ℝ → ℝ) (hN : ∀ ω, MonotoneOn (N ω) (Ici 0)) (h0 : ∀ ω, N ω 0 = 0)
    (hM : ∀ t, Measurable (fun ω => N ω t))
    (hid : ∀ j : ℕ, IdentDistrib (fun ω => N ω ((j:ℝ)+1) - N ω j) (fun ω => N ω 1) P P)
    (h2 : Integrable (fun ω => (N ω 1)^2) P) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => P {ω |
      ∃ t ∈ Icc (0:ℝ) 1,
        ε ≤ |(N ω ((n:ℝ)*t) - (n:ℝ)*t)/Real.sqrt n -
          walkInterp (fun j ω => N ω ((j:ℝ)+1) - N ω j - 1) n ω ((n:ℝ)*t)/Real.sqrt n|})
      atTop (𝓝 0) := by sorry
