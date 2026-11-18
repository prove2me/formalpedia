-- Prove2me | Theorems.Thm_OWMR_mirror_candidate_cost
-- name    : OWMR.mirror_candidate_cost
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T20:47:32.222195+00:00
-- url     : https://prove2.me/theorems/8d85e8b4-f0ce-4676-8744-373e61305122
-- title:
--   Lemma 4 (mirror bounds and candidate cost): B_w≤βw and B_w≤hE[X_w]≤hw/2; a shifted width-w candidate has augmented cost G+(K-∫g(υ+x)U(dx))/M(w)+B_w
-- statement:
--   Fix a retailer $i$ under the standing assumptions, with $F=F_i$, actual setup cost $K=K_i$, renewal measure $U$ and $M(w)=U[0,w)$. For $w>0$ let $X_w$ have the law $U(\cdot\cap[0,w))/M(w)$ (the long-run depletion of a width-$w$ policy, (10)), and let $B_w=\min_z\mathbb E[p(z-X_w)^++h(X_w-z)^+]$ be its mirror cost (14), with the minimum written as an infimum. Then:
--   1. For every $w>0$, $X_w$ is a probability law, $B_w\le\beta w$ and $B_w\le h\,\mathbb EX_w\le hw/2$, where $\beta=hp/(h+p)$.
--   2. Let $(\hat s,\hat S)$ be a canonical optimum at a planning setup cost $k>0$, $G=J(k)$ and $g(x)=G-F(\hat S-x)$. For $0<w\le\hat w$ and $0\le\upsilon\le\hat w-w$, the width-$w$ policy with target $\hat S-\upsilon$ (the $(s,S)$ policy with $s=\hat S-\upsilon-w$ and $S=\hat S-\upsilon$), started at its target and charged the actual setup cost $K$, has augmented average cost (average setup, holding and backlog cost plus its mirror cost, `augCost`) equal to $G+(K-\int_{[0,w)}g(\upsilon+x)\,U(dx))/M(w)+B_w$, which is (15).
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 4.3, Lemma 4 (Mirror Bounds and Candidate Cost) with the mirror cost (14), the candidate cost (15), the depletion law of (10) and the augmented cost of Section 3, pp. 13 and 16.

import Definitions.Def_owmr_renewal

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem mirror_candidate_cost {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n)
    (k sh Sh : ℝ) (hk : 0 < k) (hcan : IsCanonicalOptimum (N.marginal i) (N.F i) k sh Sh)
    (X : ℝ → Measure ℝ) (hX : ∀ w, X w = (renewalMeasure (N.marginal i) (Set.Ico 0 w))⁻¹
      • (renewalMeasure (N.marginal i)).restrict (Set.Ico 0 w))
    (B : ℝ → ℝ)
    (hB : ∀ w, B w = ⨅ z : ℝ, ∫ y, (N.p * max (z - y) 0 + N.h * max (y - z) 0) ∂(X w)) :
    (∀ w, 0 < w → IsProbabilityMeasure (X w) ∧
      B w ≤ N.h * N.p / (N.h + N.p) * w ∧
      B w ≤ N.h * ∫ y, y ∂(X w) ∧ N.h * ∫ y, y ∂(X w) ≤ N.h * w / 2) ∧
    ∃ G : ℝ, 0 < G ∧ N.J i k = ENNReal.ofReal G ∧
      ∀ w υ : ℝ, 0 < w → w ≤ Sh - sh → 0 ≤ υ → υ ≤ Sh - sh - w →
        N.augCost i (Sh - υ - w) (Sh - υ) = ENNReal.ofReal (G
          + (N.K i - ∫ y in Set.Ico 0 w, (G - N.F i (Sh - (υ + y))) ∂(renewalMeasure (N.marginal i)))
            / (renewalMeasure (N.marginal i) (Set.Ico 0 w)).toReal + B w) := by sorry
end OWMR
