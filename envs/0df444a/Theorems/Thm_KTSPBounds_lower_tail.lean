-- Prove2me | Theorems.Thm_KTSPBounds_lower_tail
-- name    : KTSPBounds.lower_tail
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:38:05.108845+00:00
-- url     : https://prove2.me/theorems/5e4fc7bf-083c-4385-85cc-dd382575277a
-- title:
--   Proof of the lower bound in Theorem 2, p.10 — tail display
-- statement:
--   Under the assumptions of Theorem 2, for every $n \ge 2$, $2 \le k \le n$ and $\varepsilon > 0$,
--
--   $$
--   \mathbb P\left[ l_{TSP}(k,n) \le \varepsilon \sqrt{\frac{2}{e^2\pi}} \, \frac{k-1}{n^{\frac12\left(1+\frac1{k-1}\right)}} \sqrt{\mathcal A_{\mathcal K}} \right] \le \frac{\varepsilon^{2k-2}}{2\sqrt{\pi(k-1)}}.
--   $$
--
--   The scale in this bound is the scale of the lower bound of Theorem 2.
--
--   Differences from the source:
--   - encoding: a chain of displayed inequalities → the first and the last term of the chain; reason: the middle terms are proof steps; the chain asserts exactly this comparison
--   - encoding: compact 𝒦 ⊂ ℝ² with area 𝒜_𝒦 → IsCompact K, 0 < volume K, area (volume K).toReal; reason: the uniform law is undefined at area 0, so the hypothesis excludes only an undefined case; compactness gives finite area
--   - encoding: n vertices drawn independently, uniformly on 𝒦 → sampleMeasure (uniformLaw K) n, the product of n copies of Lebesgue measure on K normalized by its area; reason: the Lean rendering of the same law on EuclideanSpace ℝ (Fin 2)
--   - encoding: l_TSP(k, n), the optimal value of (2) over endogenous subsets of k vertices → kTSPLength k x, the minimum over embeddings Fin k ↪ Fin n of the path length; reason: an embedding is a choice of k distinct sample indices in an order; this is the same minimum
-- source:
--   Blanchard, Jacquillat, Jaillet, Probabilistic bounds on the k-Traveling Salesman Problem and the Traveling Repairman Problem, arXiv:2211.11063v1, proof of the lower bound in Theorem 2, p.10

import Mathlib
import Definitions.Def_WassersteinDRO_Guarantees_sampleMeasure
import Definitions.Def_KTSPBounds_uniformLaw
import Definitions.Def_KTSPBounds_kTSPLength
import Definitions.Def_KTSPBounds_rate

open MeasureTheory

namespace KTSPBounds

/-- The tail display in the proof of the lower bound of Theorem 2, p.10, Blanchard, Jacquillat, Jaillet, arXiv:2211.11063v1:
`ℙ[l_TSP(k, n) ≤ ε √(2/(e²π)) (k-1)/n^{½(1+1/(k-1))} √𝒜_𝒦] ≤ ε^{2k-2} / (2√(π(k-1)))`.

**Formalization Note.** `e` is `Real.exp 1`, and `rate n k` is `(k-1)/n^{½(1+1/(k-1))}`. The
order of the factors on the left is the paper's. -/
theorem lower_tail (K : Set Plane) (hK : IsCompact K) (hvol : 0 < volume K)
    (n k : ℕ) (hn : 2 ≤ n) (hk : 2 ≤ k) (hkn : k ≤ n) (ε : ℝ) (hε : 0 < ε) :
    WassersteinDRO.Guarantees.sampleMeasure (uniformLaw K) n {x | kTSPLength k x ≤
        ε * Real.sqrt (2 / (Real.exp 1 ^ 2 * Real.pi)) * rate n k *
          Real.sqrt (volume K).toReal} ≤
      ENNReal.ofReal (ε ^ (2 * k - 2) / (2 * Real.sqrt (Real.pi * ((k : ℝ) - 1)))) := by sorry

end KTSPBounds
