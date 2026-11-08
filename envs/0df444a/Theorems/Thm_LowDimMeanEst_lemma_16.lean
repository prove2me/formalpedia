-- Prove2me | Theorems.Thm_LowDimMeanEst_lemma_16
-- name    : LowDimMeanEst.lemma_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:56:08.960248+00:00
-- url     : https://prove2.me/theorems/8283fd5f-8471-44d7-bae6-6921cbfb23b9
-- title:
--   Lemma 16 — for $\tau_0\ge\sqrt{nd/\log(1/\delta)}$, w.p. $\ge1-\delta/100$: $\frac1n\sum_{\|x_i\|\le\tau_0}\|x_i\|^2\le2d+\frac{4\tau_0^2}n\log\frac{100}\delta$
-- statement:
--   **Lemma 16.** Let $d,n\ge1$, $\delta\in(0,\frac13]$, and let $D$ be a distribution on $\mathbb R^d$ with mean $\mu$, $\|\mu\|\le1$ and covariance $\Sigma\preceq I$; let $x_1,\dots,x_n$ be i.i.d. from $D$. For every $\tau_0\ge\sqrt{nd/\log(1/\delta)}$, with probability at least $1-\delta/100$,
--
--   $$\frac1n\sum_{i:\|x_i\|\le\tau_0}\|x_i\|^2\ \le\ 2d+\frac{4\tau_0^2}{n}\log\frac{100}\delta .$$
--
--   With $\tau_0=\tau=\sqrt{nd}$ this is event F, which controls the Lipschitz analysis of the small-norm samples in §8.1.
--
--   Differences from the source:
--   - encoding: d, n implicit → 1 ≤ d and 1 ≤ n; reason: standing assumptions: d ≥ 1 (p.13, Lemma 25) and n samples; only excludes degenerate cases
--   - encoding: δ ≤ 1/3 → 0 < δ ≤ 1/3; reason: δ is a probability parameter
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Lemma 16, p.24

import Mathlib
import Definitions.Def_LowDimMeanEst_Basic

open MeasureTheory

namespace LowDimMeanEst

/-- **Lemma 16**, p.24.

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…).

"Suppose the probability parameter δ ≤ 1/3. Now consider a distribution D on ℝᵈ with mean µ
satisfying ∥µ∥ ≤ 1 and covariance matrix Σ ⪯ I. Let x₁, …, xₙ denote n i.i.d. samples drawn from D.
For any τ₀ ≥ √(nd/log(1/δ)), it holds with probability at least 1 − δ/100 that
(1/n) Σ_{i:∥xᵢ∥≤τ₀} ∥xᵢ∥² ≤ 2d + (4τ₀²/n) log(100/δ)."

**Formalization Note.** `d ≥ 1`, `n ≥ 1` and `δ > 0` are the paper's standing assumptions; the
failure probability of the complement is bounded by `δ/100`.
-/
theorem lemma_16 {d n : ℕ} (hd : 1 ≤ d) (hn : 1 ≤ n) (δ : ℝ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 3)
    (D : Measure (E d)) [IsProbabilityMeasure D] (hD : CovLe D 1) (hmu : ‖popMean D‖ ≤ 1)
    (τ0 : ℝ) (hτ : Real.sqrt (n * d / logInv δ) ≤ τ0) :
    (Measure.pi fun _ : Fin n => D)
        {x | 2 * d + 4 * τ0 ^ 2 / n * Real.log (100 / δ) <
          (1 / (n : ℝ)) * ∑ i ∈ Finset.univ.filter (fun i => ‖x i‖ ≤ τ0), ‖x i‖ ^ 2} ≤
      ENNReal.ofReal (δ / 100) := by sorry

end LowDimMeanEst
