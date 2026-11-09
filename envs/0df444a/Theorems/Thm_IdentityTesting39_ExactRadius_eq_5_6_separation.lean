-- Prove2me | Theorems.Thm_IdentityTesting39_ExactRadius_eq_5_6_separation
-- name    : IdentityTesting39.ExactRadius.eq_5_6_separation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:54:57.717468+00:00
-- url     : https://prove2.me/theorems/db5921de-3931-4892-b339-09fb18d9e8d5
-- title:
--   §4, (5)–(6) — separating gradients and deterministic signals
-- statement:
--   Let $q$ be a finite probability reference, $\varepsilon$ a nonempty strict radius, and $n>0$. For any applicable nonempty moment branch of value $J>0$, there exist an optimizer $(r^*,w^*,e^*,d^*)$ and $\theta\in[0,1]$ supported on the active costs. With the explicit gradients
--
--   $$a_i=1-\frac{4q_i^2}{(r_i^*+q_i)^2},\qquad b_i=\frac{w_i^*(2q_i^2+w_i^*)}{(q_i^2+w_i^*)^2}\quad(i\in I),$$
--
--   and $b_i=0$ off $I$, the first-order separating inequality holds against every feasible tuple. At zero reference coordinates the active derivatives are one. The coordinate bounds are $-3\le a_i\le1$, $0\le b_i\le1$. Moreover $n\sum q_i a_i^2\le9J$, $n^2\sum q_i^2b_i^2\le4J$, $a\cdot(r^*-q)\ge M(r^*)$, and $b\cdot w^*\ge C_I(w^*)$.
--
--   The active weighted cost equals $J$. Every deterministic feasible probability vector $p$ has weighted linear-plus-quadratic signal at least $J$, and consequently
--
--   $$n\sum_i a_i(p_i-q_i)\ge J\quad\text{or}\quad n^2\sum_i b_i(p_i-q_i)^2\ge J.$$
--
--   This supplies the coefficients of the statistical upper test.
--
--   Differences from the source:
--   - encoding: a finite domain with k labels → an arbitrary finite label type ι, with k its cardinality; reason: finite relabeling changes no instance and permits the reservoir quotient
--   - encoding: minima over scalar tuples on the relevant coordinates → law-defined moments, real infima with explicit attainment where asserted, and zero unused head slots; reason: zeroing unused slots is a coordinate convention; infeasible deficit values are never used
--   - encoding: derivatives at q_i=0 equal one → explicit cases in both gradient definitions; b_i=0 outside I; reason: the printed zero-coordinate convention is preserved rather than using 0/0 for b_i
-- source:
--   Zhijie Zheng, An Exact-Radius Convex Characterization of Discrete Identity Testing, STOC 2027 submission #39 (October 2026), p.4, §4, displays (5)–(6), continuing on p.5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/39.pdf

import Definitions.Def_IdentityTesting39_ExactRadius_PoissonExperiments

open scoped BigOperators

namespace IdentityTesting39.ExactRadius

/-- §4, (5)–(6), printed pp.4–5 / PDF pp.5–6. -/
theorem eq_5_6_separation {ι : Type} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (ε n : ℝ) (B : Branch ι)
    (hq : ProbabilityVector q) (hε : StrictRadius q ε) (hn : 0 < n)
    (hregime : InRegime q B)
    (hfeas : (feasibleMoments q ε B).Nonempty) (hJ : 0 < programValue q ε n B) :
    ∃ x : MomentFamily ι, ∃ θ : ℝ, SeparatingOptimizer q ε n B x θ ∧
      (∀ i, -3 ≤ aVector q x i ∧ aVector q x i ≤ 1 ∧
        0 ≤ bVector q B x i ∧ bVector q B x i ≤ 1) ∧
      n*(∑ i, q i*(aVector q x i)^2) ≤ 9*programValue q ε n B ∧
      n^2*(∑ i, (q i)^2*(bVector q B x i)^2) ≤ 4*programValue q ε n B ∧
      meanCost q x ≤ ∑ i, aVector q x i*(x i 0-q i) ∧
      quadraticCost q B x ≤ ∑ i, bVector q B x i*x i 1 ∧
      θ*n*meanCost q x + (1-θ)*n^2*quadraticCost q B x = programValue q ε n B ∧
      ∀ p, ProbabilityVector p → deterministicTuple q p B ∈ feasibleMoments q ε B →
        programValue q ε n B ≤
          θ*n*(∑ i, aVector q x i*(p i-q i)) +
          (1-θ)*n^2*(∑ i, bVector q B x i*(p i-q i)^2) ∧
        (programValue q ε n B ≤ n*(∑ i, aVector q x i*(p i-q i)) ∨
          programValue q ε n B ≤ n^2*(∑ i, bVector q B x i*(p i-q i)^2)) := by sorry

end IdentityTesting39.ExactRadius
