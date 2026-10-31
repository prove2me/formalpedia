-- Prove2me | Theorems.Thm_KTSPBounds_upper_bound_corrected
-- name    : KTSPBounds.upper_bound_corrected
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:38:18.370324+00:00
-- url     : https://prove2.me/theorems/3486ed9c-3df9-4d24-844a-af55f7a91ab2
-- title:
--   Theorem 2, upper bound, pp.12–13 (corrected: $\sqrt{\mathcal A_{\mathcal K}} \to \operatorname{diam}\mathcal K$)
-- statement:
--   There is a universal constant $C > 0$ such that, for every compact $\mathcal K \subset \mathbb R^2$ of positive area, every $n \ge 2$ and every $2 \le k \le n$,
--
--   $$
--   \mathbb E[l_{TSP}(k,n)] \le C \, \frac{k-1}{n^{\frac12\left(1+\frac1{k-1}\right)}} \operatorname{diam}(\mathcal K).
--   $$
--
--   This is the upper half of Theorem 2 in corrected form.
--
--   Differences from the source:
--   - correction: upper bound with √𝒜_𝒦 → upper bound with Metric.diam K; reason: the printed bound is false. Take 𝒦_s = [0,1]×[0,s], 0 < s ≤ 1, n = k = 2: every assumption holds, 𝔼[l_TSP(2,2)] ≥ 𝔼|U₁−U₂| = 1/3 for U₁, U₂ i.i.d. uniform on [0,1], and the printed bound is C√s/2, below 1/3 once s < 4/(9C²). On a square diam(𝒦) = √(2𝒜_𝒦), so the corrected bound gives the printed one there with C√2
--   - encoding: for some universal constant → the existential quantifier stands before K, n and k; reason: this is what universal means
--   - encoding: compact 𝒦 ⊂ ℝ² with area 𝒜_𝒦 → IsCompact K, 0 < volume K, area (volume K).toReal; reason: the uniform law is undefined at area 0, so the hypothesis excludes only an undefined case; compactness gives finite area
--   - encoding: n vertices drawn independently, uniformly on 𝒦 → sampleMeasure (uniformLaw K) n, the product of n copies of Lebesgue measure on K normalized by its area; reason: the Lean rendering of the same law on EuclideanSpace ℝ (Fin 2)
--   - encoding: l_TSP(k, n), the optimal value of (2) over endogenous subsets of k vertices → kTSPLength k x, the minimum over embeddings Fin k ↪ Fin n of the path length; reason: an embedding is a choice of k distinct sample indices in an order; this is the same minimum
--   - encoding: 𝔼[l_TSP(k, n)] → the Bochner integral of kTSPLength k against sampleMeasure (uniformLaw K) n; reason: the integrand is measurable and almost surely bounded, so the integral is the expectation (proved in the sanity file)
-- source:
--   Blanchard, Jacquillat, Jaillet, Probabilistic bounds on the k-Traveling Salesman Problem and the Traveling Repairman Problem, arXiv:2211.11063v1, Theorem 2 and proof of the upper bound, pp.9 and 12–13

import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_sampleMeasure
import Definitions.Def_KTSPBounds_uniformLaw
import Definitions.Def_KTSPBounds_kTSPLength
import Definitions.Def_KTSPBounds_rate

open MeasureTheory

namespace KTSPBounds

/-- The upper bound of Theorem 2, pp.12–13, Blanchard, Jacquillat, Jaillet, arXiv:2211.11063v1, corrected: there is a universal
constant `C > 0` with `𝔼[l_TSP(k, n)] ≤ C (k-1)/n^{½(1+1/(k-1))} diam(𝒦)` for every compact `K`
of positive area, every `n ≥ 2` and every `2 ≤ k ≤ n`.

**Formalization Note.** The paper prints `√𝒜_𝒦` where this statement has `diam(𝒦)`. The printed
bound is false: for `𝒦_s = [0,1] × [0,s]` and `n = k = 2`, the expectation is at least `1/3` while
the printed bound is `C√s/2`. `Metric.diam K` is the true diameter because a compact set is
bounded. `C` is quantified before `K`, `n` and `k`. -/
theorem upper_bound_corrected :
    ∃ C : ℝ, 0 < C ∧ ∀ K : Set Plane, IsCompact K → 0 < volume K →
      ∀ n k : ℕ, 2 ≤ n → 2 ≤ k → k ≤ n →
        ∫ x, kTSPLength k x ∂(WassersteinDRO.Guarantees.sampleMeasure (uniformLaw K) n) ≤ C * rate n k * Metric.diam K := by sorry

end KTSPBounds
