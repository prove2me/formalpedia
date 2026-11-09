-- Prove2me | Theorems.Thm_HighConfRobust_fact_3_1
-- name    : HighConfRobust.fact_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:05:31.735201+00:00
-- url     : https://prove2.me/theorems/801e575d-fd4b-4748-aa8f-c44877a0591e
-- title:
--   Fact 3.1 — TV-close distributions are mixtures with a common component
-- statement:
--   Let $P$ and $Q$ be probability distributions with
--
--   $$
--   \mathrm{TV}(P,Q)\le\varepsilon\le 1 .
--   $$
--
--   Then there exist probability distributions $G$, $H_1$, $H_2$ such that
--
--   $$
--   P=(1-\varepsilon)\,G+\varepsilon\,H_1\qquad\text{and}\qquad Q=(1-\varepsilon)\,G+\varepsilon\,H_2 .
--   $$
--
--   This coupling form of total variation lets the proof of Lemma 4.3 write both distributions as convex combinations of three common laws.
--
--   **Formalization Note** Total variation is `MarkovChainCLT.tvDist`; the mixture weights are the nonnegative extended reals $\max(1-\varepsilon,0)$ and $\max(\varepsilon,0)$, which are $1-\varepsilon$ and $\varepsilon$ because $0\le\mathrm{TV}(P,Q)\le\varepsilon\le1$.
--
--   Differences from the source:
--   - encoding: weights 1 − ε and ε of a mixture of distributions → ℝ≥0∞ scalars ENNReal.ofReal (1 − ε), ENNReal.ofReal ε on measures; reason: equal to 1 − ε and ε since 0 ≤ TV(P, Q) ≤ ε ≤ 1; same instances
-- source:
--   Narayanan–Lee–Pensia, High Confidence Yields Outlier Robustness, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153), Fact 3.1, p.16

import Mathlib
import Definitions.Def_TotalVariationDist

namespace HighConfRobust

open MeasureTheory

/-- **Fact 3.1** (p.16). If `TV(P, Q) ≤ ε ≤ 1` for probability measures `P, Q`, then there are
probability measures `G, H₁, H₂` with `P = (1 − ε) G + ε H₁` and `Q = (1 − ε) G + ε H₂`.

Narayanan–Lee–Pensia, *High Confidence Yields Outlier Robustness: Consequences in Computational
Hardness, Privacy, and Replicability*, STOC 2027 submission manuscript, Nov. 3, 2026
(sha256 f0e4ec41…c370c153), Fact 3.1, p.16.

**Formalization Note** TV is the public `MarkovChainCLT.tvDist`. The mixture weights are the
`ℝ≥0∞` scalars `ENNReal.ofReal (1 − ε)` and `ENNReal.ofReal ε`; `0 ≤ ε` follows from `TV ≥ 0`. -/
theorem fact_3_1 {X : Type*} [MeasurableSpace X] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (ε : ℝ)
    (hPQ : MarkovChainCLT.tvDist P Q ≤ ε) (hε : ε ≤ 1) :
    ∃ G H₁ H₂ : Measure X, IsProbabilityMeasure G ∧ IsProbabilityMeasure H₁ ∧
      IsProbabilityMeasure H₂ ∧
      P = ENNReal.ofReal (1 - ε) • G + ENNReal.ofReal ε • H₁ ∧
      Q = ENNReal.ofReal (1 - ε) • G + ENNReal.ofReal ε • H₂ := by sorry

end HighConfRobust
