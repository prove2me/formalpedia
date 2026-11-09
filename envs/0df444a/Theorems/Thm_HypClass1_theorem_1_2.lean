-- Prove2me | Theorems.Thm_HypClass1_theorem_1_2
-- name    : HypClass1.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:40:33.251843+00:00
-- url     : https://prove2.me/theorems/3ed702e2-94be-4a06-a1ed-d8bc4aeec7a8
-- title:
--   Theorem 1.2 — $H^{(3)}_{n,p}$ is Class 1 w.h.p. for $n^{-2/3-1/200}\le p\le 0.99$
-- statement:
--   Let $p = p(n)$ satisfy
--   $$
--   n^{-2/3-1/200} \le p \le 0.99 .
--   $$
--   Then a random 3-graph $H \sim H^{(3)}_{n,p}$ with high probability satisfies
--   $$
--   \chi'(H) = \Delta(H),
--   $$
--   that is, $\mathbb P_{n,p(n)}[\chi'(H) = \Delta(H)] \to 1$ as $n \to \infty$.
--
--   This is the 3-uniform analogue of the theorem of Erdős and Wilson that almost every graph is Class 1. For uniformity $k \ge 4$ and $k \nmid n$ the analogue fails (Proposition 1.3).
--
--   **Formalization Note** $p : \mathbb N \to \mathbb R$ is an arbitrary sequence satisfying the two bounds for all sufficiently large $n$; nothing else (monotonicity, a limit) is assumed. Every $n$ counts, with no divisibility condition.
--
--   Differences from the source:
--   - reading: p := p(n) with n^{−2/3−1/200} ≤ p ≤ 0.99 → the bounds hold for all sufficiently large n (∀ᶠ n in atTop); reason: at n = 1 the bounds read 1 ≤ p ≤ 0.99, so requiring them for every n would make the theorem vacuous; the statement is asymptotic
--   - reading: 'with high probability' (never defined in the paper) → probability → 1 as n → ∞ (Tendsto … atTop (𝓝 1)); reason: the standard meaning
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Theorem 1.2, p.3

import Mathlib
import Definitions.Def_HypClass1_binomProb
import Definitions.Def_HypClass1_chromaticIndex
import Definitions.Def_MatchVec3_maxDegree

open Filter Topology

namespace HypClass1

/-- **Theorem 1.2 (almost every 3-graph is Class 1).** Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Theorem 1.2, p.3:
"For p := p(n) satisfying n^{−2/3−1/200} ≤ p ≤ 0.99, a random 3-graph H ∼ H^{(3)}_{n,p} with high
probability satisfies χ′(H) = ∆(H)."

**Formalization Note.** `p : ℕ → ℝ` is any sequence with `n^{−2/3−1/200} ≤ p(n) ≤ 0.99` for all large
`n` (at `n = 1` the bounds read `1 ≤ p ≤ 0.99`, so they cannot hold for every `n`); "with high
probability" is `P[χ′(H) = ∆(H)] → 1` as `n → ∞`. `H ∼ H^{(3)}_{n,p}` on the vertex set `Fin n`
(`binomProb`). Every `n` counts (no divisibility condition). -/
theorem theorem_1_2 (p : ℕ → ℝ)
    (hp : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (-(2 / 3 + 1 / 200 : ℝ)) ≤ p n ∧ p n ≤ 0.99) :
    Tendsto (fun n : ℕ => binomProb n (p n) (fun H => chromaticIndex H = MatchVec3.maxDegree H))
      atTop (𝓝 1) := by sorry

end HypClass1
