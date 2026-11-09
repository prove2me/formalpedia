-- Prove2me | Theorems.Thm_HighConfRobust_lemma_4_3
-- name    : HighConfRobust.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:07:06.172363+00:00
-- url     : https://prove2.me/theorems/d4c98bca-abf3-452a-b25c-18af92c14845
-- title:
--   Lemma 4.3 — a reference distribution TV-close to $P$ and Rényi-close to $Q$
-- statement:
--   Let $P$ and $Q$ be probability distributions with $\mathrm{TV}(P,Q)\le\varepsilon$ for some $\varepsilon\in(0,1]$, and let $a\in(0,1)$. Set
--
--   $$
--   \kappa:=\frac{1}{\max(1,\log(\varepsilon/a))}\in(0,1].
--   $$
--
--   Then there exists a probability distribution $F$ such that
--
--   1. $\mathrm{TV}(P,F)\le a$, and
--   2. $D_q(Q\,\|\,F)\le\dfrac{2\varepsilon}{\kappa}$ for $q=1+\kappa\in(1,2]$.
--
--   The distribution $F$ is the reference law of the reduction: it is close enough to the clean law $P$ that the high-confidence guarantee applies to it, and close enough to the contaminated law $Q$ in Rényi divergence that failure probabilities transfer.
--
--   **Formalization Note** Total variation is `MarkovChainCLT.tvDist` and $D_q$ the mission's `renyiDivergence`. The claim $\kappa\in(0,1]$ is part of the conclusion; $q\in(1,2]$ follows from it.
--
--   Differences from the source: none.
-- source:
--   Narayanan–Lee–Pensia, High Confidence Yields Outlier Robustness, STOC 2027 submission manuscript, Nov. 3, 2026 (sha256 f0e4ec41…c370c153), Lemma 4.3, p.17

import Mathlib
import Definitions.Def_TotalVariationDist
import Definitions.Def_HighConfRobust_renyiDivergence

namespace HighConfRobust

open MeasureTheory

/-- **Lemma 4.3** (p.17). Let `P, Q` be probability measures with `TV(P, Q) ≤ ε` for some
`ε ∈ (0, 1]`, and let `a ∈ (0, 1)`. Then `κ := 1 / max(1, log(ε/a)) ∈ (0, 1]`, and there is a
probability measure `F` with
1. `TV(P, F) ≤ a`, and
2. `D_q(Q ‖ F) ≤ 2ε/κ` for `q = 1 + κ ∈ (1, 2]`.

Narayanan–Lee–Pensia, *High Confidence Yields Outlier Robustness: Consequences in Computational
Hardness, Privacy, and Replicability*, STOC 2027 submission manuscript, Nov. 3, 2026
(sha256 f0e4ec41…c370c153), Lemma 4.3, p.17.

**Formalization Note** TV is the public `MarkovChainCLT.tvDist`; `D_q` is
`HighConfRobust.renyiDivergence`. The clause `κ ∈ (0, 1]` is part of the conclusion; `q ∈ (1, 2]`
follows from it. -/
theorem lemma_4_3 {X : Type*} [MeasurableSpace X] (P Q : Measure X)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (ε a : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hPQ : MarkovChainCLT.tvDist P Q ≤ ε) (ha : 0 < a) (ha1 : a < 1) :
    let κ : ℝ := 1 / max 1 (Real.log (ε / a))
    (0 < κ ∧ κ ≤ 1) ∧
      ∃ F : Measure X, IsProbabilityMeasure F ∧ MarkovChainCLT.tvDist P F ≤ a ∧
        renyiDivergence (1 + κ) Q F ≤ ((2 * ε / κ : ℝ) : EReal) := by sorry

end HighConfRobust
