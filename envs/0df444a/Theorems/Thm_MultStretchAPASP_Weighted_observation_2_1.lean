-- Prove2me | Theorems.Thm_MultStretchAPASP_Weighted_observation_2_1
-- name    : MultStretchAPASP.Weighted.observation_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:10:47.384521+00:00
-- url     : https://prove2.me/theorems/2fce32cd-5ee3-4ca6-9f94-d99423f60d5e
-- title:
--   Observation 2.1 — a Bernoulli(q) sample of n vertices has size Õ(nq) w.h.p.
-- statement:
--   Let $q\in(0,1)$ and let $S\subseteq V$, $|V|=n\ge1$, be obtained by sampling each vertex independently with probability $q$. Then $|S|\in\tilde O(nq)$ with high probability: for every $c>0$ there is a constant $C$ such that for every $n\ge1$ and every $q\in(0,1)$,
--   $$\Pr\Bigl[\,|S|>C\,n\,q\,(\log_2(n+2))^C+C\,\Bigr]\ \le\ n^{-c}.$$
--
--   The bound controls the number of pivots $|S_1|$ and hence the inner dimension of the products of Algorithm 10.
--
--   Differences from the source:
--
--   - encoding: a vertex set V with |V| = n → Fin n with 1 ≤ n; reason: a fixed vertex type; n ≥ 1 makes log n and n^(−c) meaningful
--   - reading: Õ(nq) → C·(log₂(n + 2))^C·(nq) + C with one constant C fixed before the instance; reason: Õ hides polylogarithmic factors in n (§2.2, p. 5); the additive C and n + 2 keep the bound meaningful at small n
--   - reading: with high probability (probability ≥ 1 − n^{−c} for any fixed c > 0, constants depending on c; p. 5) → for every c > 0 a constant C with failure measure (outer measure of the set of bad outcomes) at most n^(−c); reason: the paper's own definition of w.h.p.; the measure of the failure set avoids measurability side conditions
--   - encoding: S sampled vertex by vertex with probability q → the product law sampleLaw n q on indicator vectors, S = sampled x; reason: the same distribution
-- source:
--   Saggi, Sapir, Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime, arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), p. 5, Observation 2.1

import Mathlib
import Definitions.Def_MultStretchAPASP_Weighted_Sampling
import Definitions.Def_DynConnWC_Program
import Definitions.Def_MinKCutII_Main_Runs
import Definitions.Def_MultStretchAPASP_Weighted_Graph
import Definitions.Def_MultStretchAPASP_Weighted_MinPlus
import Definitions.Def_MultStretchAPASP_Weighted_Encoding

set_option autoImplicit false

namespace MultStretchAPASP.Weighted

/-- **Observation 2.1** (p. 5, from [27]). Let `S` be obtained by sampling each of the `n` vertices
independently with probability `q ∈ (0, 1)`. Then `|S| ∈ Õ(nq)` with high probability: for every
`c > 0` there is a constant `C` such that for every `n ≥ 1` and every `q ∈ (0, 1)`,
`Pr[|S| > C·n·q·(log₂(n + 2))^C + C] ≤ n^{−c}`. -/
theorem observation_2_1 :
    ∀ c : ℝ, 0 < c → ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ q : ℝ, 0 < q → q < 1 →
      sampleLaw n q {x | (C : ℝ) * n * q * polylog n C + C < ((sampled x).card : ℝ)} ≤
        ENNReal.ofReal ((n : ℝ) ^ (-c)) := by sorry

end MultStretchAPASP.Weighted
