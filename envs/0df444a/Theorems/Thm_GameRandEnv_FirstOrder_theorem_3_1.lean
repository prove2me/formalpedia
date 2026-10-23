-- Prove2me | Theorems.Thm_GameRandEnv_FirstOrder_theorem_3_1
-- name    : GameRandEnv.FirstOrder.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:26:44.427433+00:00
-- url     : https://prove2.me/theorems/8159534d-cfdd-44e0-bca4-898397e794cb
-- title:
--   Theorem 3.1, p. 4 — first-order condition: minimizers of F + ηH over Π satisfy ∇ₓδF/δπ̄ + η∇ₓ ln π*(·|y) = 0, and for convex F the converse holds
-- statement:
--   **Theorem 3.1 (first-order condition).** Let $\mathbb Y$ be a Polish space carrying a probability measure $\mathsf m$, let $p\ge1$, and let $\Pi$ be the set of probability measures on $\mathbb R^d\times\mathbb Y$ with $\mathbb Y$-marginal $\mathsf m$ and finite $p$-th moment. Let $F:\Pi\to\mathbb R$ satisfy Assumption 2.1, with linear functional derivative $\frac{\delta F}{\delta\bar\pi}$. For $\eta>0$ define
--   $$V(\bar\pi):=F(\bar\pi)+\eta H(\bar\pi),$$
--   where $H(\bar\pi)$ is the relative entropy of $\bar\pi$ with respect to $\mathrm{Leb}\times\mathsf m$. Then:
--   1. if $\bar\pi^*\in\operatorname{argmin}_{\bar\pi\in\Pi}V(\bar\pi)$, then $\bar\pi^*$ has a density $\pi^*(x|y)$ with respect to $\mathrm{Leb}\times\mathsf m$ such that for $\mathsf m$-a.e. $y$ it is positive and log-differentiable in $x$ and
--   $$\nabla_x\frac{\delta F}{\delta\bar\pi}(\bar\pi^*,x,y)+\eta\nabla_x\ln\pi^*(x|y)=0\qquad\text{for all }x\in\mathbb R^d;\tag{3.1}$$
--   2. conversely, if $F$ is in addition convex on $\Pi$, then every $\bar\pi^*\in\Pi$ satisfying (3.1) belongs to $\operatorname{argmin}_{\bar\pi\in\Pi}V(\bar\pi)$.
--
--   The theorem characterizes entropy-regularized minimizers over measures with a prescribed environment marginal as fixed points of a Gibbs-type equation, $\pi^*(x|y)\propto\exp(-\frac1\eta\frac{\delta F}{\delta\bar\pi}(\bar\pi^*,x,y))$. It is the basis of the paper's necessary condition for Nash equilibria of games on a random environment (Corollary 3.3) and identifies the invariant measure of the mean-field Langevin system.
--
--   **Formalization Note** (3.1) is read as a statement about some version of the density (any version may be modified on null sets, and the gradient of an arbitrary version is meaningless), required for $\mathsf m$-a.e. $y$ and every $x$. Convexity of $F$ is along mixtures inside $\Pi$. $\mathbb Y$ is a complete separable metric space with its Borel $\sigma$-algebra. $H$ and $V$ take values in $(-\infty,+\infty]$, with $H=+\infty$ off absolute continuity. Assumption 2.1 additionally makes explicit the measurability and integrability that the defining identity (2.1) presupposes.
-- source:
--   Conforti, Kazeykina, Ren, Game on random environment, mean-field Langevin system and neural networks, arXiv:2004.02457v2, p. 4, Theorem 3.1

import Mathlib
import Definitions.Def_GameRandEnv_FirstOrder_Setting

open MeasureTheory Filter Topology

namespace GameRandEnv.FirstOrder

theorem theorem_3_1 {d : ℕ} {Y : Type*} [MetricSpace Y] [CompleteSpace Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (m : Measure Y) [IsProbabilityMeasure m] (p : ℝ)
    (F : Measure (Rd d × Y) → ℝ) (δF : Measure (Rd d × Y) → Rd d → Y → ℝ)
    (hA : Assumption21 m p F δF) (η : ℝ) (hη : 0 < η)
    (πs : Measure (Rd d × Y)) :
    (IsMinimizer m p F η πs → FirstOrderCondition m δF η πs) ∧
    (ConvexOnPi m p F → πs ∈ Pi m p → FirstOrderCondition m δF η πs →
      IsMinimizer m p F η πs) := by sorry

end GameRandEnv.FirstOrder
