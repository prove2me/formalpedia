-- Prove2me | Theorems.Thm_KTSPBounds_theorem_2
-- name    : KTSPBounds.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:38:09.277426+00:00
-- url     : https://prove2.me/theorems/9e6c3904-7df0-4b29-a106-9dfe734d01ff
-- title:
--   Theorem 2, p.9 — $\mathbb E[l_{TSP}(k,n)]$ is of order $(k-1)/n^{\frac12(1+\frac1{k-1})}$ (corrected: $\sqrt{\mathcal A_{\mathcal K}} \to \operatorname{diam}\mathcal K$ in the upper bound)
-- statement:
--   There are universal constants $0 < c < C$ such that the following holds. Let $n$ vertices be drawn independently and uniformly on a compact set $\mathcal K \subset \mathbb R^2$ of area $\mathcal A_{\mathcal K} > 0$, and let $l_{TSP}(k,n)$ be the length of the $k$-TSP on these vertices. Then, for all $n \ge 2$ and $2 \le k \le n$,
--
--   $$
--   c \, \frac{k-1}{n^{\frac12\left(1+\frac1{k-1}\right)}} \sqrt{\mathcal A_{\mathcal K}} \le \mathbb E[l_{TSP}(k,n)] \le C \, \frac{k-1}{n^{\frac12\left(1+\frac1{k-1}\right)}} \operatorname{diam}(\mathcal K).
--   $$
--
--   The result gives the order of the expected $k$-TSP length for every $k$, not only asymptotically. It interpolates between the smallest pairwise distance, of order $1/n$ at $k = 2$, and the Beardwood–Halton–Hammersley rate $\sqrt n$ at $k = n$.
--
--   Differences from the source:
--   - correction: upper bound with √𝒜_𝒦 → upper bound with Metric.diam K; reason: the printed bound is false. Take 𝒦_s = [0,1]×[0,s], 0 < s ≤ 1, n = k = 2: every assumption holds, 𝔼[l_TSP(2,2)] ≥ 𝔼|U₁−U₂| = 1/3 for U₁, U₂ i.i.d. uniform on [0,1], and the printed bound is C√s/2, below 1/3 once s < 4/(9C²). On a square diam(𝒦) = √(2𝒜_𝒦), so the corrected bound gives the printed one there with C√2
--   - encoding: for all n ≥ 2 and 2 ≤ k ≤ n, for some universal constants 0 < c < C → ∃ c C, 0 < c ∧ c < C ∧ ∀ K n k; reason: universal means independent of 𝒦, n and k, so the constants stand first
--   - encoding: compact 𝒦 ⊂ ℝ² with area 𝒜_𝒦 → IsCompact K, 0 < volume K, area (volume K).toReal; reason: the uniform law is undefined at area 0, so the hypothesis excludes only an undefined case; compactness gives finite area
--   - encoding: n vertices drawn independently, uniformly on 𝒦 → sampleMeasure (uniformLaw K) n, the product of n copies of Lebesgue measure on K normalized by its area; reason: the Lean rendering of the same law on EuclideanSpace ℝ (Fin 2)
--   - encoding: l_TSP(k, n), the optimal value of (2) over endogenous subsets of k vertices → kTSPLength k x, the minimum over embeddings Fin k ↪ Fin n of the path length; reason: an embedding is a choice of k distinct sample indices in an order; this is the same minimum
--   - encoding: 𝔼[l_TSP(k, n)] → the Bochner integral of kTSPLength k against sampleMeasure (uniformLaw K) n; reason: the integrand is measurable and almost surely bounded, so the integral is the expectation (proved in the sanity file)
-- source:
--   Blanchard, Jacquillat, Jaillet, Probabilistic bounds on the k-Traveling Salesman Problem and the Traveling Repairman Problem, arXiv:2211.11063v1, Theorem 2, p.9

import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_sampleMeasure
import Definitions.Def_KTSPBounds_uniformLaw
import Definitions.Def_KTSPBounds_kTSPLength
import Definitions.Def_KTSPBounds_rate

open MeasureTheory

namespace KTSPBounds

/-- Theorem 2, p.9, Blanchard, Jacquillat, Jaillet, arXiv:2211.11063v1, with the upper bound corrected: there are universal
constants `0 < c < C` such that, for every compact `K ⊂ ℝ²` of positive area `𝒜_𝒦`, every `n ≥ 2`
and every `2 ≤ k ≤ n`, the `k`-TSP on `n` independent uniform points of `K` satisfies
`c (k-1)/n^{½(1+1/(k-1))} √𝒜_𝒦 ≤ 𝔼[l_TSP(k, n)] ≤ C (k-1)/n^{½(1+1/(k-1))} diam(𝒦)`.

**Formalization Note.** The lower bound is the printed one. The upper bound has `diam(𝒦)` where
the paper prints `√𝒜_𝒦`. The printed upper bound is false: for `𝒦_s = [0,1] × [0,s]` and
`n = k = 2`, the expectation is at least `1/3` while the printed bound is `C√s/2`. On a square,
`diam(𝒦) = √(2𝒜_𝒦)`, so the printed bound follows there with the constant `C√2`. The constants are
quantified before `K`, `n` and `k`. The expectation is a Bochner integral of a measurable function
that is bounded almost surely, so it is not a junk value. -/
theorem theorem_2 :
    ∃ c C : ℝ, 0 < c ∧ c < C ∧ ∀ K : Set Plane, IsCompact K → 0 < volume K →
      ∀ n k : ℕ, 2 ≤ n → 2 ≤ k → k ≤ n →
        c * rate n k * Real.sqrt (volume K).toReal ≤ ∫ x, kTSPLength k x ∂(WassersteinDRO.Guarantees.sampleMeasure (uniformLaw K) n) ∧
          ∫ x, kTSPLength k x ∂(WassersteinDRO.Guarantees.sampleMeasure (uniformLaw K) n) ≤ C * rate n k * Metric.diam K := by sorry

end KTSPBounds
