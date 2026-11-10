-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_nearly_optimal_ppr
-- name    : NearlyOptimalPPR.Computation.nearly_optimal_ppr
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T06:38:50.806606+00:00
-- url     : https://prove2.me/theorems/20e97e63-e97e-4f33-a72a-91e0c83e43da
-- title:
--   Theorem 1.2 — Nearly optimal PPR independent of teleportation
-- statement:
--   Fix an idealized exact-SDDM primitive model with $C_s>0$ and polynomial-logarithmic exponent $p_s\in\mathbb N$. There exist one admissible scalar/query program $\mathcal A$ and absolute positive constants $C,c$, depending only on this fixed model, such that the following holds for every finite simple unweighted undirected graph in arbitrary adjacency-list order, every seed $s$, and all real $0<\alpha<1$, $0<\varepsilon\le1$. The program is fixed before graph size, source and parameters; it receives only $s,\alpha,\varepsilon$ and accesses the graph locally.
--
--   It terminates almost surely with a nonnegative explicit sparse output $\widehat\pi_s$ satisfying the ACL guarantee at every vertex. An isolated seed is returned exactly as $e_s$. Work $W$ is measurable and nonnegative, and nontermination has work infinity. With $K=1/\varepsilon$,
--
--   $$\mathbb E W\le C K\exp\!\left(c\sqrt{\log(2K)\log\log(4K)}\right).$$
--
--   For every $\eta>0$, the displayed envelope is at most $K^{1+\eta}$ for all sufficiently large $K$, with a threshold independent of $G,s,\alpha$. Thus the bound is $K^{1+o(1)}$ uniformly in teleportation.
--
--   The explicit-output lower bound is retained. For each fixed $0<\alpha<1$, let $\beta=(1-\alpha)/(2-\alpha)$. Whenever $0<\varepsilon\le\beta/4$, the star with $L=\lfloor\beta/(2\varepsilon)\rfloor$ leaves and center source has
--
--   $$\pi_s(s)=\frac1{2-\alpha},\qquad \pi_s(v)=\frac\beta L\quad(v\ne s),\qquad L\ge\frac\beta{4\varepsilon}\ge1.$$
--
--   Every ACL-accurate output has each leaf estimate at least $\varepsilon$ and requires at least $\beta/(4\varepsilon)$ emitted entries. Every program execution prefix has charged work at least its number of emitted entries. The lower-bound coefficient may depend on the fixed $\alpha$; the upper-bound constants may not.
--
--   This is the paper's full near-optimality statement in its exact-solve model. It does not assert this cost for finite-precision approximate SDDM solvers. No recurrence, correctness invariant, termination certificate, or runtime bound is a hypothesis of the program.
--
--   Differences from the source:
--   - reading: there exists an algorithm in the arithmetic/adjacency-list exact-SDDM model → one admissible finite scalar/query program, with constants fixed before every graph and real parameter; reason: the specified machine disallows arbitrary graph-dependent instructions and free parameter preparation
--   - encoding: O(epsilon^(-1-o(1))) expected work independent of alpha → C K exp(c sqrt(log(2K) log log(4K))) together with the eventual exponent-1+eta bound; reason: Lemma 4.5 pp.18–19 supplies this full quantitative envelope; C and c depend only on the fixed primitive model
--   - encoding: fixed-alpha explicit-output Omega(1/epsilon) star lower bound → beta=(1-alpha)/(2-alpha), epsilon<=beta/4, L=floor(beta/(2epsilon)) and at least beta/(4epsilon) emitted entries; reason: this spells out the p.2 asymptotic argument and charges every emitted entry
--   - encoding: the nonnegative algorithm output and exact isolated-source branch → these behaviors are included with ACL accuracy in the success conclusion; reason: they are specified by the source algorithms and the standing convention on p.4
-- source:
--   Rong-Hua Li, Quanqing Xu, Yichun Yang, Junjie Zhou, STOC 2027 submission #884 (October 2026), Theorem 1.2 and explicit-output paragraph p.2; §2 p.4; quantitative Lemma 4.5 pp.18–19

import Mathlib
import Definitions.Def_NearlyOptimalPPR_Computation_push

set_option autoImplicit false

open Finset Matrix MeasureTheory
open scoped ENNReal

namespace NearlyOptimalPPR.Computation

/-- Li, Xu, Yang, Zhou, STOC 2027 submission #884 (October 2026),
Theorem 1.2 and explicit-output lower bound p.2; quantitative envelope
Lemma 4.5 pp.18--19. The exact-SDDM idealization is part of the model. -/
theorem nearly_optimal_ppr (m : SolveModel) :
    ∃ (p : Program) (C c : ℝ), admissible p ∧ 0 < C ∧ 0 < c ∧
      (∀ (n : ℕ) (g : InputGraph n) (s : Fin n) (α ε : ℝ),
        0 < α → α < 1 → 0 < ε → ε ≤ 1 →
          successful m p g s α ε ∧
          Measurable (executionWork m p g s α ε) ∧
          expectedWork m p g s α ε ≤ ENNReal.ofReal (envelope C c ε)) ∧
      subpolynomialEnvelope C c ∧
      explicitOutputLowerBound ∧
      (∀ (p' : Program) (n : ℕ) (g : InputGraph n) (s : Fin n)
        (α ε : ℝ) (ω : ℕ → Bool) (t : ℕ),
        ((machineRun m p' g s α ε ω t).output.length : ℝ≥0∞) ≤
          (machineRun m p' g s α ε ω t).work) := by sorry

end NearlyOptimalPPR.Computation
