-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_stieltjes_integrals_stable_under_uniform_weight_and_primitive_limits
-- name    : ManyServerQED.Scheduling.stieltjes_integrals_stable_under_uniform_weight_and_primitive_limits
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:43:56.363938+00:00
-- url     : https://prove2.me/theorems/62c747e8-88fe-47ee-89c0-94429965d078
-- title:
--   Stability of weighted drift integrals from compact path convergence
-- statement:
--   Let bounded right-continuous weights converge uniformly to a continuous limit on a compact interval. If a sequence of uniformly Lipschitz primitives converges pointwise to an integral primitive, then their right-endpoint weighted sums define integrals which converge to the weighted integral against the limiting density.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_ManyServerQED_Scheduling_weighted_lipschitz_path_has_measurable_drift_density
import Theorems.Thm_ManyServerQED_Scheduling_integrated_drift_continuous_weight_limit
import Theorems.Thm_ManyServerQED_Scheduling_right_endpoint_stieltjes_sums_for_cadlag_weight
open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open ManyServerQED.Scheduling Finset

theorem ManyServerQED.Scheduling.stieltjes_integrals_stable_under_uniform_weight_and_primitive_limits (T C D : ℝ) (hT : 0 ≤ T) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (v A : ℕ → ℝ → ℝ) (w B b : ℝ → ℝ)
    (hv : ∀ n t, t ∈ Icc (0:ℝ) T → ContinuousWithinAt (v n) (Ici t) t)
    (hvb : ∀ n t, t ∈ Icc (0:ℝ) T → |v n t| ≤ D)
    (hV : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t ∈ Icc (0:ℝ) T, |v n t-w t| < ε)
    (hW : ContinuousOn w (Icc (0:ℝ) T))
    (hA : ∀ n s t, s ∈ Icc (0:ℝ) T → t ∈ Icc (0:ℝ) T →
      |A n t-A n s| ≤ C*|t-s|)
    (hAB : ∀ t ∈ Icc (0:ℝ) T, Tendsto (fun n => A n t) atTop (𝓝 (B t)))
    (hB : ∀ t ∈ Icc (0:ℝ) T, (∫ s in (0:ℝ)..t,b s) = B t-B 0)
    (hb : IntervalIntegrable b volume 0 T) (hbb : ∀ t ∈ Icc (0:ℝ) T, |b t| ≤ C) :
    ∃ z : ℕ → ℝ, (∀ n, Tendsto (fun m : ℕ => ∑ j ∈ range (m+1),
      v n (T*(j+1:ℕ)/(m+1:ℕ)) *
      (A n (T*(j+1:ℕ)/(m+1:ℕ))-A n (T*j/(m+1:ℕ)))) atTop (𝓝 (z n))) ∧
      Tendsto z atTop (𝓝 (∫ s in (0:ℝ)..T,w s*b s)) := by sorry
