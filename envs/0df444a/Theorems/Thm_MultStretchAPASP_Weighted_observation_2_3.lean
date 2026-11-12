-- Prove2me | Theorems.Thm_MultStretchAPASP_Weighted_observation_2_3
-- name    : MultStretchAPASP.Weighted.observation_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T07:10:56.778534+00:00
-- url     : https://prove2.me/theorems/d6433912-ee63-476e-aeef-0fd319fa7cdd
-- title:
--   Observation 2.3 — |E_S| = Õ(n/q) w.h.p. for a Bernoulli(q) sample S
-- statement:
--   Let $G=(V,E,w)$ be an undirected graph on $n\ge1$ vertices with non-negative weights, let $q\in(0,1)$ and let $S$ be obtained by sampling each vertex independently with probability $q$. With $E_S=\bigcup_{u\in V}\{(u,v)\in E: w(u,v)<\delta(u,S)\}$, $|E_S|\in\tilde O(n/q)$ with high probability: for every $c>0$ there is a constant $C$ such that for every $n\ge1$, every $q\in(0,1)$ and every such graph,
--   $$\Pr\Bigl[\,|E_S|>C\,\frac nq\,(\log_2(n+2))^C+C\,\Bigr]\ \le\ n^{-c}.$$
--
--   The bound controls the size of $G_1=(V,E_1,w)$, on which Algorithm 5 runs in lines 9 and 28.
--
--   Differences from the source:
--
--   - encoding: a vertex set V with |V| = n → Fin n with 1 ≤ n; reason: a fixed vertex type; n ≥ 1 makes log n and n^(−c) meaningful
--   - encoding: an undirected graph G = (V, E, w) with w : E → ℝ≥0 → a symmetric weight matrix w : Fin n → Fin n → ℝ≥0∞ with ⊤ on the diagonal (IsWGraph), w x y = ⊤ meaning no edge; distances δ in ℝ≥0∞ (⊤ for disconnected pairs); reason: same graphs; ℝ≥0∞ represents the paper's ∞ exactly, so no junk value arises for disconnected pairs
--   - reading: Õ(n/q) → C·(log₂(n + 2))^C·(n/q) + C with one constant C fixed before the instance; reason: Õ hides polylogarithmic factors in n (§2.2, p. 5); the additive C and n + 2 keep the bound meaningful at small n
--   - reading: with high probability (probability ≥ 1 − n^{−c} for any fixed c > 0, constants depending on c; p. 5) → for every c > 0 a constant C with failure measure (outer measure of the set of bad outcomes) at most n^(−c); reason: the paper's own definition of w.h.p.; the measure of the failure set avoids measurability side conditions
--   - encoding: E_S as a set of edges (u, v) → edgesBelow w S, the set of unordered pairs s(u, v) with w(u, v) < δ(u, S); reason: an undirected edge is counted once
-- source:
--   Saggi, Sapir, Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime, arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), p. 5, Observation 2.3

import Mathlib
import Definitions.Def_MultStretchAPASP_Weighted_Sampling
import Definitions.Def_DynConnWC_Program
import Definitions.Def_MinKCutII_Main_Runs
import Definitions.Def_MultStretchAPASP_Weighted_Graph
import Definitions.Def_MultStretchAPASP_Weighted_MinPlus
import Definitions.Def_MultStretchAPASP_Weighted_Encoding

set_option autoImplicit false

namespace MultStretchAPASP.Weighted

/-- **Observation 2.3** (p. 5, from [27]). For an undirected graph `w` with non-negative weights
on `n` vertices and `S` obtained by sampling each vertex independently with probability
`q ∈ (0, 1)`, the edge set `E_S = ⋃_u {(u, v) ∈ E | w(u, v) < δ(u, S)}` has `|E_S| ∈ Õ(n/q)` with
high probability: for every `c > 0` there is a constant `C` such that for every `n ≥ 1`, every
`q ∈ (0, 1)` and every such graph, `Pr[|E_S| > C·(n/q)·(log₂(n + 2))^C + C] ≤ n^{−c}`. -/
theorem observation_2_3 :
    ∀ c : ℝ, 0 < c → ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ q : ℝ, 0 < q → q < 1 →
      ∀ w : WMat n, IsWGraph w →
        sampleLaw n q
            {x | (C : ℝ) * (n / q) * polylog n C + C < ((edgesBelow w (sampled x)).card : ℝ)} ≤
          ENNReal.ofReal ((n : ℝ) ^ (-c)) := by sorry

end MultStretchAPASP.Weighted
