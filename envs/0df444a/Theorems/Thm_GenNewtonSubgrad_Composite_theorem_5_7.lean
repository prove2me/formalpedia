-- Prove2me | Theorems.Thm_GenNewtonSubgrad_Composite_theorem_5_7
-- name    : GenNewtonSubgrad.Composite.theorem_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:52.846328+00:00
-- url     : https://prove2.me/theorems/b6d8fe72-0ae1-4189-994f-14432c22d26e
-- title:
--   Theorem 5.7 — local Q-superlinear convergence of the Newton-type Algorithm 5.3 for $C^{1,1}$ functions
-- statement:
--   Let $\varphi:\mathbb R^n\to\mathbb R$ be of class $C^{1,1}$ around $\bar x$, and let $\bar x$ solve the gradient equation $\nabla\varphi(\bar x)=0$ (1.1). Assume the standing assumptions (H1)–(H3) for the gradient mapping $\nabla\varphi$ at $(\bar x,0)$:
--
--   1. (H1) there are neighbourhoods $U$ of $\bar x$ and $V$ of $0$ such that for every $x\in U$ with $\nabla\varphi(x)\in V$ some direction $d$ satisfies $-\nabla\varphi(x)\in(D^*\nabla\varphi)(x)(d)$;
--   2. (H2) $\nabla\varphi$ is metrically regular around $(\bar x,0)$;
--   3. (H3) $\nabla\varphi$ is semismooth\* at $(\bar x,0)$.
--
--   Then there is a neighbourhood $U$ of $\bar x$ such that Algorithm 5.3 is well-defined from every starting point $x^0\in U$, and every sequence $\{x^k\}$ it generates from $x^0\in U$ converges Q-superlinearly to $\bar x$:
--   $$x^k\to\bar x\quad\text{and}\quad\lim_{k\to\infty}\frac{\|x^{k+1}-\bar x\|}{\|x^k-\bar x\|}=0 .$$
--
--   This is the local convergence theorem for the $C^{1,1}$ Newton scheme; the composite algorithm of §7 reduces to it through the forward-backward envelope.
--
--   **Formalization Note** $\partial^2\varphi(x)$ for a $C^{1,1}$ function is the coderivative $D^*\nabla\varphi(x)$ of the single-valued gradient map. Q-superlinear convergence is stated in $\varepsilon$-form (for every $\varepsilon>0$, eventually $\|x^{k+1}-\bar x\|\le\varepsilon\|x^k-\bar x\|$), which avoids the ratio $0/0$ after a stop at $\bar x$. "Well-defined" means every partial run from $U$ can be continued; the conclusion holds for every run, i.e. for every admissible choice of directions. This statement is identical to the Theorem 5.7 item of the companion mission on prox-regular functions.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 20, Theorem 5.7

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Alg53

open Filter Topology
open scoped InnerProductSpace

namespace GenNewtonSubgrad.Composite

/-- Theorem 5.7 (p. 20): local Q-superlinear convergence of Algorithm 5.3 for a `C^{1,1}`
function `φ` at a solution `x̄` of `∇φ(x) = 0` under (GenNewtonSubgrad.ProxReg.H1)–(H3) on `∇φ` at `(x̄, 0)`. -/
theorem theorem_5_7 {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (xbar : EuclideanSpace ℝ (Fin n))
    (hC11 : GenNewtonSubgrad.ProxReg.IsC11Around φ xbar) (hsol : gradient φ xbar = 0)
    (hH : GenNewtonSubgrad.ProxReg.StandingH (GenNewtonSubgrad.ProxReg.sv (gradient φ)) xbar 0) :
    ∃ U ∈ 𝓝 xbar, GenNewtonSubgrad.ProxReg.Alg53WellDefinedOn φ U ∧
      ∀ x : ℕ → EuclideanSpace ℝ (Fin n), GenNewtonSubgrad.ProxReg.IsAlg53Run φ x → x 0 ∈ U → GenNewtonSubgrad.ProxReg.IsQSuperlinear x xbar := by sorry

end GenNewtonSubgrad.Composite
