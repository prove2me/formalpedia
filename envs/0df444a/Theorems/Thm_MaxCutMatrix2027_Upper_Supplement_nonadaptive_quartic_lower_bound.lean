-- Prove2me | Theorems.Thm_MaxCutMatrix2027_Upper_Supplement_nonadaptive_quartic_lower_bound
-- name    : MaxCutMatrix2027.Upper.Supplement.nonadaptive_quartic_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:09:56.074209+00:00
-- url     : https://prove2.me/theorems/6bf82a34-dbf6-452c-84ea-a76a7d0c6c89
-- title:
--   Theorem 6.1 (companion theorem) — Non-adaptive quartic lower bound
-- statement:
--   There is an absolute constant $c>0$ such that the following holds for every $0<\varepsilon\le 0.005$ and every integer $n\ge\lceil1/\varepsilon^2\rceil$. Let a randomized non-adaptive tester for MAX-CUT on $n$-vertex graphs be given: a probability space of private seeds $\omega$ and, for each seed, a fixed set of queried unordered pairs and an arbitrary real-valued output function of their answers. If on every simple graph $G$
--   $$\Pr_\omega\bigl(|\widehat M_\omega(G)-\mathrm{MAXCUT}(G)|\le\varepsilon n^2\bigr)\ge\frac23,$$
--   and every seed queries at most $Q$ distinct pairs, then
--   $$Q\ge\frac{c}{\varepsilon^4}.$$
--
--   This is the paper's non-adaptive lower bound, matching the $O(1/\varepsilon^4)$ upper bound of the mission's goal (Theorem 4.1) up to the constant. The proof on p.31 works with $c=1/(16e^2\cdot40^4)$.
--
--   Differences from the source:
--   - encoding: vertices (variables) labelled by [n] → Fin n = {0,…,n−1}; reason: relabeling is bijective
--   - encoding: randomized non-adaptive tester with internal randomness and unrestricted computation → an arbitrary probability space of seeds with, for each seed, a fixed set of unordered non-diagonal query pairs and an arbitrary real function of their answers; per-graph success events are required measurable; reason: this is the model of §3 p.13; a success probability presupposes a measurable event
--   - encoding: requires Ω(1/ε⁴) pair queries in the worst case → one absolute c > 0 chosen before ε, n and the tester, with c/ε⁴ ≤ Q for every Q bounding the number of distinct queried pairs on every seed; reason: definition of Ω and of worst-case query complexity (§3 p.13)
--   - encoding: 0.005 → 1/200; reason: same number
-- source:
--   Songhua He, STOC 2027 submission #351 (October 2026), Theorem 6.1, p.29 (PDF p.29); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/351.pdf; PDF SHA-256 b38cd84079663d9e2eb7375d7bf1572d5dc7c2157cfaf90e175fd371a9503631

import Definitions.Def_MaxCutMatrix2027_Upper_Supplement_QueryModel
set_option autoImplicit false
open MeasureTheory

universe u₆

namespace MaxCutMatrix2027.Upper.Supplement

/-- Theorem 6.1, p.29. A randomized non-adaptive estimator is an arbitrary probability space of
private seeds `ω` and a deterministic non-adaptive algorithm `A ω` for each seed. If it makes at
most `Q` distinct pair queries on every seed and succeeds with probability at least `2/3` on
every graph, then `Q ≥ c/ε⁴`, for one absolute `c > 0` chosen before all parameters. -/
theorem nonadaptive_quartic_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 200 → ∀ n : ℕ, ⌈1 / ε ^ 2⌉₊ ≤ n →
      ∀ (Ω : Type u₆) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : Ω → NonAdaptiveQuery n) (Q : ℕ),
        (∀ ω, (A ω).pairs.card ≤ Q) →
        (∀ G : SimpleGraph (Fin n),
          MeasurableSet {ω | Accurate ε G ((A ω).output G)} ∧
          ENNReal.ofReal (2 / 3) ≤ μ {ω | Accurate ε G ((A ω).output G)}) →
        c / ε ^ 4 ≤ (Q : ℝ) := by sorry

end MaxCutMatrix2027.Upper.Supplement
