-- Prove2me | Theorems.Thm_HypClass1_theorem_9_1
-- name    : HypClass1.theorem_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:29:04.741558+00:00
-- url     : https://prove2.me/theorems/0fcbef56-992d-4094-a398-8298d0af8f6e
-- title:
--   Theorem 9.1 — the maximum-degree vertex beats every other by $\sqrt{pn^2}/\log^2 n$
-- statement:
--   Let $p = p(n)$ satisfy $\log^4 n / n^2 \le p \le 0.99$. Then with high probability $H \sim H^{(3)}_{n,p}$ has the following property: if $x^\star$ is a vertex of maximum degree, then
--   $$
--   \deg_H(x^\star) - \deg_H(y) \ge \frac{\sqrt{pn^2}}{\log^2 n} \qquad \text{for every vertex } y \ne x^\star .
--   $$
--   In particular the vertex of maximum degree is unique. This degree gap is what allows every colour class of an optimal colouring to pass through $x^\star$.
--
--   **Formalization Note** The event says: every vertex $x$ with $\deg_H(x) = \Delta(H)$ beats every other vertex by the stated margin.
--
--   Differences from the source:
--   - reading: p := p(n) with log⁴ n/n² ≤ p ≤ 0.99 → the bounds hold for all sufficiently large n; reason: the statement is asymptotic
--   - reading: 'with high probability' (never defined in the paper) → probability → 1 as n → ∞ (Tendsto … atTop (𝓝 1)); reason: the standard meaning
--   - reading: 'If x⋆ ∈ V(H) is the vertex of maximum degree' → for every vertex x with deg_H(x) = ∆(H); reason: covers every candidate for x⋆; the positive gap forces uniqueness (Observation 2.1)
--   - reading: log (base not named) → natural logarithm Real.log; reason: standard convention; paper.md decision 6
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Theorem 9.1, p.46

import Mathlib
import Definitions.Def_HypClass1_binomProb
import Definitions.Def_MatchVec3_maxDegree
import Definitions.Def_HypClass1_deg

open Filter Topology

namespace HypClass1

/-- **Theorem 9.1 (degree gap of the maximum-degree vertex).** Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Theorem 9.1, p.46:
"For p := p(n) satisfying log⁴ n/n² ≤ p ≤ 0.99, a random 3-graph H ∼ H^{(3)}_{n,p} with high
probability satisfies the following. If x⋆ ∈ V(H) is the vertex of maximum degree, then
deg(x⋆) − deg(y) ≥ √(pn²)/log² n for every y ∈ V(H) ∖ {x⋆}."

**Formalization Note.** `p(n)` satisfies the bounds for all large `n`; "with high probability" is
`P → 1`. The event: every vertex `x⋆` of degree `∆(H)` beats every other vertex `y` by at least
`√(p n²)/(log n)²` (so `x⋆` is unique). `log` is the natural logarithm. -/
theorem theorem_9_1 (p : ℕ → ℝ)
    (hp : ∀ᶠ n : ℕ in atTop, Real.log n ^ 4 / (n : ℝ) ^ 2 ≤ p n ∧ p n ≤ 0.99) :
    Tendsto (fun n : ℕ => binomProb n (p n) (fun H =>
        ∀ x : Fin n, deg H x = MatchVec3.maxDegree H → ∀ y : Fin n, y ≠ x →
          Real.sqrt (p n * (n : ℝ) ^ 2) / Real.log n ^ 2 ≤ (deg H x : ℝ) - deg H y))
      atTop (𝓝 1) := by sorry

end HypClass1
