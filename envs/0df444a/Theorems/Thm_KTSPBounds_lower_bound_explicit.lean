-- Prove2me | Theorems.Thm_KTSPBounds_lower_bound_explicit
-- name    : KTSPBounds.lower_bound_explicit
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:38:01.886774+00:00
-- url     : https://prove2.me/theorems/380600dd-3416-4b32-a7bb-d0e50902b3ef
-- title:
--   Proof of the lower bound in Theorem 2, p.11 — explicit constant
-- statement:
--   Under the assumptions of Theorem 2, for every $n \ge 2$ and $2 \le k \le n$,
--
--   $$
--   \mathbb E[l_{TSP}(k,n)] \ge \sqrt{\frac{2}{e^2\pi}} \, \frac{k-1}{n^{\frac12\left(1+\frac1{k-1}\right)}} \sqrt{\mathcal A_{\mathcal K}} \left( 1 - \frac{1}{6\sqrt\pi} \right).
--   $$
--
--   This is the lower half of Theorem 2 with the paper's explicit constant.
--
--   Differences from the source:
--   - encoding: a chain of displayed inequalities → the first and the last term of the chain; reason: the middle terms are proof steps; the chain asserts exactly this comparison
--   - encoding: compact 𝒦 ⊂ ℝ² with area 𝒜_𝒦 → IsCompact K, 0 < volume K, area (volume K).toReal; reason: the uniform law is undefined at area 0, so the hypothesis excludes only an undefined case; compactness gives finite area
--   - encoding: n vertices drawn independently, uniformly on 𝒦 → sampleMeasure (uniformLaw K) n, the product of n copies of Lebesgue measure on K normalized by its area; reason: the Lean rendering of the same law on EuclideanSpace ℝ (Fin 2)
--   - encoding: l_TSP(k, n), the optimal value of (2) over endogenous subsets of k vertices → kTSPLength k x, the minimum over embeddings Fin k ↪ Fin n of the path length; reason: an embedding is a choice of k distinct sample indices in an order; this is the same minimum
--   - encoding: 𝔼[l_TSP(k, n)] → the Bochner integral of kTSPLength k against sampleMeasure (uniformLaw K) n; reason: the integrand is measurable and almost surely bounded, so the integral is the expectation (proved in the sanity file)
-- source:
--   Blanchard, Jacquillat, Jaillet, Probabilistic bounds on the k-Traveling Salesman Problem and the Traveling Repairman Problem, arXiv:2211.11063v1, proof of the lower bound in Theorem 2, p.11

import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_sampleMeasure
import Definitions.Def_KTSPBounds_uniformLaw
import Definitions.Def_KTSPBounds_kTSPLength
import Definitions.Def_KTSPBounds_rate

open MeasureTheory

namespace KTSPBounds

/-- The end of the proof of the lower bound of Theorem 2, p.11, Blanchard, Jacquillat, Jaillet, arXiv:2211.11063v1:
`𝔼[l_TSP(k, n)] ≥ √(2/(e²π)) (k-1)/n^{½(1+1/(k-1))} √𝒜_𝒦 (1 - 1/(6√π))`.

**Formalization Note.** The expectation is the Bochner integral of `kTSPLength k` against the
sample law. No integrability hypothesis appears because none is needed: the integrand is
measurable and bounded by `(k-1) · diam K` almost surely. -/
theorem lower_bound_explicit (K : Set Plane) (hK : IsCompact K) (hvol : 0 < volume K)
    (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n) :
    Real.sqrt (2 / (Real.exp 1 ^ 2 * Real.pi)) * rate n k * Real.sqrt (volume K).toReal *
        (1 - 1 / (6 * Real.sqrt Real.pi)) ≤
      ∫ x, kTSPLength k x ∂(WassersteinDRO.Guarantees.sampleMeasure (uniformLaw K) n) := by sorry

end KTSPBounds
