-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_integrated_drift_continuous_weight_limit
-- name    : ManyServerQED.Scheduling.integrated_drift_continuous_weight_limit
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T21:05:27.069798+00:00
-- url     : https://prove2.me/theorems/31e5fa25-db90-4da8-a2a2-3f0988d05347
-- title:
--   Continuous-weight limit for uniformly bounded drift primitives
-- statement:
--   On a finite interval, suppose the drift densities are uniformly bounded and their primitives converge pointwise to $B$. If the integrands multiplying the densities converge uniformly to a continuous weight, the weighted integrals converge. Their limit equals the limit of the left-point Riemann sums against the increments of $B$.
-- source:
--   Supporting lemma for the proof of Atar, Mandelbaum and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Mathlib
open MeasureTheory Set Filter Topology Finset

theorem ManyServerQED.Scheduling.integrated_drift_continuous_weight_limit (T C : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C)
    (v a : ℕ → ℝ → ℝ) (w B : ℝ → ℝ)
    (hW : ContinuousOn w (Icc 0 T))
    (hV : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ s ∈ Icc (0:ℝ) T, |v n s - w s| < ε)
    (hA : ∀ n, IntervalIntegrable (a n) volume 0 T)
    (hB : ∀ n s, s ∈ Icc 0 T → |a n s| ≤ C)
    (hI : ∀ n, IntervalIntegrable (fun s => v n s * a n s) volume 0 T)
    (hPrim : ∀ t ∈ Icc 0 T, Tendsto (fun n => ∫ s in (0:ℝ)..t, a n s) atTop (𝓝 (B t))) :
    ∃ x : ℝ, Tendsto (fun n => ∫ s in (0:ℝ)..T, v n s * a n s) atTop (𝓝 x) ∧
      Tendsto (fun m : ℕ => ∑ j ∈ range (m+1),
        w (T*j/(m+1:ℕ)) * (B (T*(j+1:ℕ)/(m+1:ℕ)) - B (T*j/(m+1:ℕ))))
        atTop (𝓝 x) := by sorry
