-- Prove2me | Theorems.Thm_MemOracleLB_Optimization_lemma_3_4
-- name    : MemOracleLB.Optimization.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:35:01.134422+00:00
-- url     : https://prove2.me/theorems/72156e92-beb6-4237-a390-102462e1578e
-- title:
--   Lemma 3.4 — Flip probability preservation
-- statement:
--   Let $d\ge2$ and let $X_1,\ldots,X_d\in E_d$ have independent full-dimensional density laws $\mu_i$. Define individual flips $\nu_i$ and average $\nu=d^{-1}\sum_i\nu_i$. Fix $r$, expose $X_r=x$, and project every other row to $x^\perp$ in the explicit Householder coordinates, held fixed during refreshing. Write $\nu'_r(x)$ for the average projected flip probability. Then $\nu'_r$ is integrable and
--
--   $$\mathbb E_{X_r}\nu'_r(X_r)=\frac1{d-1}\sum_{j\ne r}\nu_j=\frac{d\nu-\nu_r}{d-1}.$$
--
--   Averaging over a uniform independent $r$ also gives
--
--   $$\frac1d\sum_r\mathbb E_{X_r}\nu'_r(X_r)=\nu.$$
--
--   Every equality in the displayed source identity and its final random-index clause is retained.
--
--   Differences from the source:
--   - encoding: real Euclidean spaces, independent rows and Gaussian relative entropy → EuclideanSpace with Fin indices, product measures and Mathlib klDiv in [0,infinity]; reason: the same spaces, independent laws and divergence values, including infinite entropy
--   - encoding: d rows and projection to dimension d-1 in any fixed orthonormal coordinates → d=m+1 with m>=1, deleting r by succAbove and using the source Householder coordinates; reason: this avoids truncated subtraction, fixes the measurable coordinates from the proof, and changes no flip probability
--   - encoding: the expected projected flip probability → its integrability is stated alongside the expectation equalities; reason: the flip is a bounded measurable probability, so the integral has its ordinary probabilistic meaning
-- source:
--   Santosh Vempala, STOC 2027 submission #365 (October 2026), Lemma 3.4, PDF p. 14 (printed p. 13), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/365.pdf

import Mathlib
import Definitions.Def_MemOracleLB_Optimization_Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace MemOracleLB.Optimization

/-- Lemma 3.4, PDF p.14 (printed p.13). Both equalities in (4) and the random-index identity. -/
theorem lemma_3_4 {m : ℕ} (hm : 1 ≤ m)
    (μ : Fin (m + 1) → Measure (E (m + 1)))
    [∀ i, IsProbabilityMeasure (μ i)] (hdensity : ∀ i, HasDensity (μ i)) :
    (∀ r : Fin (m + 1),
      Integrable (fun x => averageFlip (exposedLaws μ r x)) (μ r) ∧
      (∫ x, averageFlip (exposedLaws μ r x) ∂μ r) =
        (∑ j : Fin m, flip μ (r.succAbove j)) / m ∧
      (∑ j : Fin m, flip μ (r.succAbove j)) / m =
        ((m + 1 : ℝ) * averageFlip μ - flip μ r) / m) ∧
    ((∑ r, ∫ x, averageFlip (exposedLaws μ r x) ∂μ r) / (m + 1 : ℝ) =
      averageFlip μ) := by sorry

end MemOracleLB.Optimization
