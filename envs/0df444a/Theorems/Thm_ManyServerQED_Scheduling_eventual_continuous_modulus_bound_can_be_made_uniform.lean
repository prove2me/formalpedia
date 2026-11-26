-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_eventual_continuous_modulus_bound_can_be_made_uniform
-- name    : ManyServerQED.Scheduling.eventual_continuous_modulus_bound_can_be_made_uniform
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:13:18.405726+00:00
-- url     : https://prove2.me/theorems/a307aa5e-4db1-4a92-bdca-fbfa50cf130e
-- title:
--   An eventual modulus bound for continuous paths can be made uniform
-- statement:
--   If a sequence of continuous random paths satisfies a modulus probability estimate for every sufficiently large index, the estimate holds for every index after reducing the radius.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem ManyServerQED.Scheduling.eventual_continuous_modulus_bound_can_be_made_uniform {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {k : ℕ} [MeasurableSpace C(Icc (0:ℝ) 1, Fin k → ℝ)] [BorelSpace C(Icc (0:ℝ) 1, Fin k → ℝ)]
    (X : ℕ → Ω → C(Icc (0:ℝ) 1, Fin k → ℝ)) (hX : ∀ n, Measurable (X n))
    (e η : ℝ) (he : 0 < e) (hη : 0 < η)
    (h : ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s t : Icc (0:ℝ) 1, dist s t ≤ δ ∧ e ≤ dist (X n ω s) (X n ω t)}
        ≤ ENNReal.ofReal η) :
    ∃ d > 0, ∀ n,
      P {ω | ∃ s t : Icc (0:ℝ) 1, dist s t ≤ d ∧ e ≤ dist (X n ω s) (X n ω t)}
        ≤ ENNReal.ofReal η := by sorry
