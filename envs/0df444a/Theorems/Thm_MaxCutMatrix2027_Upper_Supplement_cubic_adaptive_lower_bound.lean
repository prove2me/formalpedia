-- Prove2me | Theorems.Thm_MaxCutMatrix2027_Upper_Supplement_cubic_adaptive_lower_bound
-- name    : MaxCutMatrix2027.Upper.Supplement.cubic_adaptive_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:12:19.050944+00:00
-- url     : https://prove2.me/theorems/31cfc7be-9f7e-40af-ac08-cb2fca2cfe3e
-- title:
--   Theorem 7.1 (companion theorem) — Cubic adaptive lower bound
-- statement:
--   There exist absolute constants $\varepsilon^*>0$ and $c>0$ such that the following holds for every $0<\varepsilon\le\varepsilon^*$ and every integer $n\ge\lceil1/\varepsilon^2\rceil$. Let a randomized adaptive tester for MAX-CUT on $n$-vertex graphs be given: a probability space of private seeds $\omega$ and, for each seed, a deterministic adaptive pair-query algorithm with real output. If on every simple graph $G$
--   $$\Pr_\omega\bigl(|\widehat M_\omega(G)-\mathrm{MAXCUT}(G)|\le\varepsilon n^2\bigr)\ge\frac{99}{100},$$
--   and on every seed and every graph at most $Q$ distinct pairs are queried, then
--   $$Q\ge\frac{c}{\varepsilon^3}.$$
--
--   This is the paper's adaptive lower bound. The argument of p.38 with Lemma 7.5 admits, for instance, $\varepsilon^*=1/160$ and $c=1/(1000\cdot40^3)$.
--
--   Differences from the source:
--   - encoding: vertices (variables) labelled by [n] → Fin n = {0,…,n−1}; reason: relabeling is bijective
--   - encoding: randomized adaptive tester with internal randomness and unrestricted computation → an arbitrary probability space of seeds with a deterministic decision tree per seed; per-graph success events are required measurable; reason: this is the model of §3 p.13; a success probability presupposes a measurable event
--   - encoding: there exists ε* > 0 ... requires Ω(1/ε³) pair queries in the worst case → absolute ε* > 0 and c > 0 chosen before ε, n and the tester, with c/ε³ ≤ Q for every Q bounding the distinct queried pairs on every seed and graph; reason: definition of Ω and of worst-case query complexity (§3 p.13)
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), Theorem 7.1, p.32 (PDF p.32); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Definitions.Def_MaxCutMatrix2027_Upper_Supplement_QueryModel
set_option autoImplicit false
open MeasureTheory

universe u₇

namespace MaxCutMatrix2027.Upper.Supplement

/-- Theorem 7.1, p.32. A randomized adaptive estimator is an arbitrary probability space of
private seeds `ω` and a deterministic adaptive decision tree `A ω` for each seed. If it makes at
most `Q` distinct pair queries on every seed and graph and succeeds with probability at least
`99/100` on every graph, then `Q ≥ c/ε³`; `ε* > 0` and `c > 0` are absolute and chosen first. -/
theorem cubic_adaptive_lower_bound :
    ∃ εstar c : ℝ, 0 < εstar ∧ 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ εstar → ∀ n : ℕ, ⌈1 / ε ^ 2⌉₊ ≤ n →
      ∀ (Ω : Type u₇) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : Ω → QueryTree n) (Q : ℕ),
        (∀ ω G, (A ω).distinctQueries G ≤ Q) →
        (∀ G : SimpleGraph (Fin n),
          MeasurableSet {ω | Accurate ε G ((A ω).output G)} ∧
          ENNReal.ofReal (99 / 100) ≤ μ {ω | Accurate ε G ((A ω).output G)}) →
        c / ε ^ 3 ≤ (Q : ℝ) := by sorry

end MaxCutMatrix2027.Upper.Supplement
