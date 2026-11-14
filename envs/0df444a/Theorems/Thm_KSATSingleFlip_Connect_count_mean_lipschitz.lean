-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_count_mean_lipschitz
-- name    : KSATSingleFlip.Connect.count_mean_lipschitz
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:41:37.959273+00:00
-- url     : https://prove2.me/theorems/e16f8807-f00c-4946-ac3f-8d522fd0c342
-- title:
--   Lipschitz comparison of fixed-count and random-count means
-- statement:
--   Let the count have any probability distribution, let g be an integrable L-Lipschitz function of the count, and suppose its mean absolute deviation from r is at most s. Then for each fixed count j the difference between g(j) and its random-count mean is at most L(|j−r|+s). This is the mean-comparison step in the Poisson-count proof of Lemma 2.6.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
set_option autoImplicit false
open MeasureTheory

theorem KSATSingleFlip.Connect.count_mean_lipschitz (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (g : ℕ → ℝ) (hg : Integrable g μ) (L r s : ℝ) (hL : 0 ≤ L)
    (hdev : Integrable (fun k : ℕ => |(k:ℝ)-r|) μ)
    (hmean : (∫ k : ℕ, |(k:ℝ)-r| ∂μ) ≤ s)
    (hlip : ∀ j k, |g j-g k| ≤ L*|(j:ℝ)-(k:ℝ)|) (j : ℕ) :
    |g j - ∫ k, g k ∂μ| ≤ L*(|(j:ℝ)-r|+s) := by sorry
