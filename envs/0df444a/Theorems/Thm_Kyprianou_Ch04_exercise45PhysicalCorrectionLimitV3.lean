-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45PhysicalCorrectionLimitV3
-- name    : Kyprianou.Ch04.exercise45PhysicalCorrectionLimitV3
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:19:24.528519+00:00
-- url     : https://prove2.me/theorems/064f2d43-0589-4fa2-b0f5-7ee467ca9618
-- title:
--   exercise45PhysicalCorrectionLimitV3
-- statement:
--   exercise45PhysicalCorrectionLimitV3
-- source:
--   Exercise 4.5(iii), physical cutoff limit

import Mathlib
open MeasureTheory Filter Set Topology
open scoped MeasureTheory NNReal ENNReal Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise45PhysicalCorrectionLimitV3
(R : Measure (ℝ × ℝ)) (t : NNReal) (hzero : R ({0} ×ˢ (univ : Set ℝ)) = 0)
    (hEn : Integrable (fun z : ℝ × ℝ => min (1 : ℝ) (z.2^2))
      (R.restrict (Ioc (0 : ℝ) (t : ℝ) ×ˢ univ)))
    (S : Finset NNReal) (j : NNReal → ℝ)
    (hR : R.restrict (Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r))
    (f g : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hf : ContinuousOn (fun z : ℝ × ℝ => f z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hg : ContinuousOn (fun z : ℝ × ℝ => g z.1 z.2) (Ici (0 : ℝ) ×ˢ univ))
    (hb : ∀ s x z : ℝ, 0 ≤ s → |f s (x+z)-f s x-z*g s x| ≤ K*z^2)
    (L : ℕ → NNReal → ℝ) (Y : NNReal → ℝ)
    (hL : ∀ n, Measurable (L n)) (hY : Measurable Y)
    (hConv : ∀ s : NNReal, 0 < s → Tendsto (fun n => L n s) atTop (nhds (Y s)))
    (e : ℕ → ℝ) (he : Tendsto e atTop (nhds 0)) :
    Tendsto (fun n => ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | e n < |x|},
      f z.1 (L n z.1.toNNReal+z.2)-f z.1 (L n z.1.toNNReal)-
        z.2*g z.1 (L n z.1.toNNReal) ∂ R)
      atTop (nhds (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ univ,
        f z.1 (Y z.1.toNNReal+z.2)-f z.1 (Y z.1.toNNReal)-
        z.2*g z.1 (Y z.1.toNNReal) ∂ R)) := by
  sorry
