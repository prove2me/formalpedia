-- Prove2me | Theorems.Thm_HypClass1_Supplement_theorem_C_5
-- name    : HypClass1.Supplement.theorem_C_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:02:23.450019+00:00
-- url     : https://prove2.me/theorems/d2d754e7-4b51-474c-be61-2dda23227d23
-- title:
--   Theorem C.5 — in $H^{(k)}_{n,p}$, $k\ge3$, the maximum-degree vertex beats every other by $\sqrt{pn^{k-1}}/\log^2 n$
-- statement:
--   Let $k\ge 3$ be a fixed integer and let $p=p(n)$ satisfy
--   $$
--   \frac{\log^4 n}{n^{k-1}}\le p\le 0.99 .
--   $$
--   Then with high probability the binomial random $k$-graph $H\sim H^{(k)}_{n,p}$ has the following property: if $x^\star$ is a vertex of maximum degree, then
--   $$
--   \deg_H(x^\star)-\deg_H(y)\ \ge\ \frac{\sqrt{p\,n^{k-1}}}{\log^2 n}\qquad\text{for every vertex } y\ne x^\star .
--   $$
--   In particular the vertex of maximum degree is unique.
--
--   This extends the mission's Theorem 9.1, its case $k=3$, to every uniformity $k\ge3$.
--
--   **Formalization Note** The event says: every vertex $x$ with $\deg_H(x)=\Delta(H)$ beats every other vertex by the stated margin. $k$ is quantified before the sequence $p(n)$ and the limit, so it does not depend on $n$.
--
--   Differences from the source:
--   - reading: p := p(n) with log⁴ n/n^{k−1} ≤ p ≤ 0.99 → the bounds hold for all sufficiently large n; reason: the statement is asymptotic; same reading as the published Theorem 9.1
--   - reading: 'whp' (never defined in the paper) → probability → 1 as n → ∞ (Tendsto … atTop (𝓝 1)); reason: the standard meaning; same reading as the published Theorem 9.1
--   - reading: 'If x⋆ ∈ V(H) is the vertex of maximum degree' → for every vertex x with deg_H(x) = ∆(H); reason: covers every candidate for x⋆; the positive gap forces uniqueness
--   - reading: log (base not named) → natural logarithm Real.log; reason: standard convention, as in the base mission
--   - reading: k ≥ 3 stated once for Appendix C (p.63) → k a fixed natural number with 3 ≤ k, quantified outside p(n) and the limit; reason: the appendix's standing assumption; k does not depend on n
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Theorem C.5, p.66 (Appendix C, k ≥ 3, p.63)

import Mathlib
import Definitions.Def_HypClass1_Supplement_binomProbK
import Definitions.Def_MatchVec3_maxDegree
import Definitions.Def_HypClass1_deg

open Filter Topology

namespace HypClass1.Supplement

/-- **Theorem C.5 (degree gap of the maximum-degree vertex of `H^{(k)}_{n,p}`).** Chatterjee, Ferber,
Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript (STOC 2027 submission,
version of 2026-11-03, sha256 ce3bba9d…), Theorem C.5, p.66 (Appendix C, k ≥ 3, p.63):
"For p := p(n) satisfying log⁴ n/n^{k−1} ≤ p ≤ 0.99, a random k-graph H := H^{(k)}_{n,p} whp satisfies
the following. If x⋆ ∈ V(H) is the vertex of maximum degree, then
deg(x⋆) − deg(y) ≥ √(pn^{k−1})/log² n for every y ∈ V(H) ∖ {x⋆}."

**Formalization Note.** `k ≥ 3` is a fixed integer, quantified outside the sequence `p(n)` and the
limit. `p(n)` satisfies the bounds for all large `n`; "whp" is `P → 1` as `n → ∞`. The event: every
vertex `x⋆` of degree `∆(H)` beats every other vertex `y` by at least `√(p n^{k−1})/(log n)²` (so `x⋆`
is unique). `n^{k−1}` is the real power with natural exponent `k − 1` (no truncation since `k ≥ 3`);
`log` is the natural logarithm. Same readings as the published `HypClass1.theorem_9_1`, its `k = 3`
case. -/
theorem theorem_C_5 (k : ℕ) (hk : 3 ≤ k) (p : ℕ → ℝ)
    (hp : ∀ᶠ n : ℕ in atTop, Real.log n ^ 4 / (n : ℝ) ^ (k - 1) ≤ p n ∧ p n ≤ 0.99) :
    Tendsto (fun n : ℕ => binomProbK k n (p n) (fun H =>
        ∀ x : Fin n, HypClass1.deg H x = MatchVec3.maxDegree H → ∀ y : Fin n, y ≠ x →
          Real.sqrt (p n * (n : ℝ) ^ (k - 1)) / Real.log n ^ 2 ≤
            (HypClass1.deg H x : ℝ) - HypClass1.deg H y))
      atTop (𝓝 1) := by sorry

end HypClass1.Supplement
