-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_right_endpoint_stieltjes_sums_for_cadlag_weight
-- name    : ManyServerQED.Scheduling.right_endpoint_stieltjes_sums_for_cadlag_weight
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:19:43.878619+00:00
-- url     : https://prove2.me/theorems/35409022-b50b-4bdb-a138-eecdadac3b62
-- title:
--   Right endpoint sums for a right-continuous drift weight
-- statement:
--   For a bounded right-continuous weight and a bounded integrable density on a compact interval, the right-endpoint weighted increments of the density primitive converge to the integral of the weight against the density.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open MeasureTheory Set Filter Topology Finset

theorem ManyServerQED.Scheduling.right_endpoint_stieltjes_sums_for_cadlag_weight (T C D : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (w a : ℝ → ℝ)
    (hw : ∀ t ∈ Icc (0:ℝ) T, ContinuousWithinAt w (Ici t) t)
    (hW : ∀ t ∈ Icc (0:ℝ) T, |w t| ≤ D)
    (ha : IntervalIntegrable a volume 0 T)
    (hA : ∀ t ∈ Icc (0:ℝ) T, |a t| ≤ C) :
    let B (t : ℝ) := ∫ s in (0:ℝ)..t,a s
    Tendsto (fun m : ℕ => ∑ j ∈ range (m+1),
      w (T*(j+1:ℕ)/(m+1:ℕ)) *
      (B (T*(j+1:ℕ)/(m+1:ℕ))-B (T*j/(m+1:ℕ)))) atTop
      (𝓝 (∫ t in (0:ℝ)..T,w t*a t)) := by sorry
