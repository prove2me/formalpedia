-- Prove2me | Theorems.Thm_LowDimMeanEst_lemma_23
-- name    : LowDimMeanEst.lemma_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:57:53.274134+00:00
-- url     : https://prove2.me/theorems/f15c45c8-a7da-43a8-9ba4-6bf9d50068bb
-- title:
--   Lemma 23 — event T (at most $4\log\frac1\delta/\log\log\frac1\delta$ samples with $\|x_i\|\ge\sqrt{nd}$) holds w.p. $\ge1-\delta/100$
-- statement:
--   **Lemma 23.** There is a universal $\delta_0\in(0,1)$ such that for all $d,n\ge1$, $\delta\in(0,\delta_0)$, and every distribution $D$ on $\mathbb R^d$ with mean $\mu$, $\|\mu\|\le1$ and covariance $\Sigma\preceq I$, $n$ i.i.d. samples from $D$ satisfy event T,
--
--   $$\#\{i:\|x_i\|\ge\sqrt{nd}\}\ \le\ \frac{4\log(1/\delta)}{\log\log(1/\delta)},$$
--
--   with probability at least $1-\delta/100$.
--
--   Few samples have large norm; this is used to add back the large-norm samples in §8.2.
--
--   Differences from the source:
--   - encoding: δ upper bounded by a small universal constant → ∃ δ0 ∈ (0, 1) chosen before d, n, D, and δ ∈ (0, δ0); reason: a universal constant
--   - encoding: d, n implicit → 1 ≤ d and 1 ≤ n; reason: standing assumptions: d ≥ 1 (p.13, Lemma 25) and n samples; only excludes degenerate cases
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Lemma 23, p.27 (proof p.28)

import Mathlib
import Definitions.Def_LowDimMeanEst_Events

open MeasureTheory

namespace LowDimMeanEst

/-- **Lemma 23**, p.27 (proof p.28).

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…).

"Suppose the probability parameter δ is upper bounded by some small universal constant. Now consider
a distribution D on ℝᵈ with mean µ satisfying ∥µ∥ ≤ 1 and covariance matrix Σ ⪯ I. Let x₁, …, xₙ
denote n i.i.d. samples drawn from D. The samples x₁, …, xₙ satisfy event T with probability at
least 1 − δ/100."

**Formalization Note.** "Some small universal constant": `∃ δ0 ∈ (0, 1)` before `d, n, D`. Event T is
Definition 21. `d ≥ 1` and `n ≥ 1` are the paper's standing assumptions.
-/
theorem lemma_23 :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 < 1 ∧
      ∀ (d n : ℕ) (δ : ℝ), 1 ≤ d → 1 ≤ n → 0 < δ → δ < δ0 →
        ∀ (D : Measure (E d)) [IsProbabilityMeasure D], CovLe D 1 → ‖popMean D‖ ≤ 1 →
          (Measure.pi fun _ : Fin n => D) {x | ¬ EventT x δ} ≤ ENNReal.ofReal (δ / 100) := by sorry

end LowDimMeanEst
