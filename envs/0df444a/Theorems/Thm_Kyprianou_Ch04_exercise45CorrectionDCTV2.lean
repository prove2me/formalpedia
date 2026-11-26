-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45CorrectionDCTV2
-- name    : Kyprianou.Ch04.exercise45CorrectionDCTV2
-- status  : Open
-- author  : @WillR
-- created : 2026-11-26T17:22:33.451116+00:00
-- url     : https://prove2.me/theorems/69e35996-0399-4edc-a436-46671a5cd1ee
-- title:
--   exercise45CorrectionDCTV2
-- statement:
--   exercise45CorrectionDCTV2
-- source:
--   Exercise 4.5(iii), pure-jump Ito limit

import Mathlib
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
open MeasureTheory ProbabilityTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45CorrectionDCTV2
    (μ : Measure (ℝ × ℝ))
    (hpos : ∀ᵐ z : ℝ × ℝ ∂μ, 0 < z.1)
    (henergy : Integrable (fun z : ℝ × ℝ => z.2^2) μ)
    (f g : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ Set.univ))
    (hg : ContinuousOn (fun z : ℝ × ℝ => g z.1 z.2) (Ici (0 : ℝ) ×ˢ Set.univ))
    (hb : ∀ s x z : ℝ, 0 ≤ s → |f s (x+z)-f s x-z*g s x| ≤ K*z^2)
    (L : ℕ → NNReal → ℝ) (Y : NNReal → ℝ)
    (hL : ∀ n, Measurable (L n)) (hY : Measurable Y)
    (hConv : ∀ t : NNReal, 0 < t → Tendsto (fun n => L n t) atTop (nhds (Y t)))
    (e : ℕ → ℝ) (he : Tendsto e atTop (nhds 0)) :
    Tendsto (fun n => ∫ z in {z : ℝ × ℝ | e n < |z.2|},
      f z.1 (L n z.1.toNNReal+z.2)-f z.1 (L n z.1.toNNReal)-
        z.2*g z.1 (L n z.1.toNNReal) ∂μ)
      atTop (nhds (∫ z, f z.1 (Y z.1.toNNReal+z.2)-f z.1 (Y z.1.toNNReal)-
        z.2*g z.1 (Y z.1.toNNReal) ∂μ)) := by
  sorry
