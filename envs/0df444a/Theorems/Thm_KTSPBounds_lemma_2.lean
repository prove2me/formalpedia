-- Prove2me | Theorems.Thm_KTSPBounds_lemma_2
-- name    : KTSPBounds.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:38:03.567483+00:00
-- url     : https://prove2.me/theorems/56fb7a18-c49d-438d-9a60-e20236a62940
-- title:
--   Lemma 2, p.9 — small-ball bound for the $k$-TSP
-- statement:
--   Let $X_1,\dots,X_n$ be independent and uniform on a compact set $\mathcal K \subset \mathbb R^2$ of area $\mathcal A_{\mathcal K} > 0$, and let $l_{TSP}(k,n)$ be the length of the $k$-TSP on these points. Then, for any $\alpha > 0$,
--
--   $$
--   \mathbb P\left[ l_{TSP}(k,n) \le \alpha \right] \le n^k \left( \frac{2\pi\alpha^2}{\mathcal A_{\mathcal K}} \right)^{k-1} \frac{1}{(2k-2)!}.
--   $$
--
--   This bound drives the lower bound of Theorem 2.
--
--   Differences from the source:
--   - generalization: implicit range 2 ≤ k ≤ n → 1 ≤ k ≤ n; reason: the k-TSP is defined for k ≤ n and k = 1 is trivial; the range contains the source range
--   - encoding: compact 𝒦 ⊂ ℝ² with area 𝒜_𝒦 → IsCompact K, 0 < volume K, area (volume K).toReal; reason: the uniform law is undefined at area 0, so the hypothesis excludes only an undefined case; compactness gives finite area
--   - encoding: n vertices drawn independently, uniformly on 𝒦 → sampleMeasure (uniformLaw K) n, the product of n copies of Lebesgue measure on K normalized by its area; reason: the Lean rendering of the same law on EuclideanSpace ℝ (Fin 2)
--   - encoding: l_TSP(k, n), the optimal value of (2) over endogenous subsets of k vertices → kTSPLength k x, the minimum over embeddings Fin k ↪ Fin n of the path length; reason: an embedding is a choice of k distinct sample indices in an order; this is the same minimum
-- source:
--   Blanchard, Jacquillat, Jaillet, Probabilistic bounds on the k-Traveling Salesman Problem and the Traveling Repairman Problem, arXiv:2211.11063v1, Lemma 2, p.9

import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_sampleMeasure
import Definitions.Def_KTSPBounds_uniformLaw
import Definitions.Def_KTSPBounds_kTSPLength

open MeasureTheory

namespace KTSPBounds

/-- Lemma 2, p.9, Blanchard, Jacquillat, Jaillet, arXiv:2211.11063v1: for `n` independent uniform points on a compact `K` of
area `𝒜_𝒦` and any `α > 0`, `ℙ[l_TSP(k, n) ≤ α] ≤ n^k (2πα²/𝒜_𝒦)^{k-1} / (2k-2)!`.

**Formalization Note.** The range `1 ≤ k ≤ n` contains the paper's implicit `2 ≤ k ≤ n`. The area
is `(volume K).toReal`, with `0 < volume K` so that the uniform law exists; it is finite because
`K` is compact. The probability is an `ℝ≥0∞` value compared with `ENNReal.ofReal` of the bound. -/
theorem lemma_2 (K : Set Plane) (hK : IsCompact K) (hvol : 0 < volume K)
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) (α : ℝ) (hα : 0 < α) :
    WassersteinDRO.Guarantees.sampleMeasure (uniformLaw K) n {x | kTSPLength k x ≤ α} ≤
      ENNReal.ofReal ((n : ℝ) ^ k * (2 * Real.pi * α ^ 2 / (volume K).toReal) ^ (k - 1) *
        (1 / ((2 * k - 2).factorial : ℝ))) := by sorry

end KTSPBounds
