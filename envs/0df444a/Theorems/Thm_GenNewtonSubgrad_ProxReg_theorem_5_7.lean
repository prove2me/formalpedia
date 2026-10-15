-- Prove2me | Theorems.Thm_GenNewtonSubgrad_ProxReg_theorem_5_7
-- name    : GenNewtonSubgrad.ProxReg.theorem_5_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:42.456985+00:00
-- url     : https://prove2.me/theorems/4d5093e8-47d7-4963-8466-e1371dcaa09c
-- title:
--   Theorem 5.7, p. 20 — local Q-superlinear convergence of the generalized Newton algorithm for $C^{1,1}$ functions
-- statement:
--   Let $\varphi:\mathbb R^n\to\mathbb R$ be of class $C^{1,1}$ around $\bar x$ with $\nabla\varphi(\bar x)=0$ (a solution of (1.1)), and assume (H1)–(H3) for the gradient mapping $\nabla\varphi$ at $(\bar x,0)$:
--
--   1. (H1) there are neighbourhoods $U$ of $\bar x$, $V$ of $0$ such that for every $x\in U$ with $\nabla\varphi(x)\in V$ some $d$ satisfies $-\nabla\varphi(x)\in\partial^2\varphi(x)(d)$ (5.2);
--   2. (H2) $\nabla\varphi$ is metrically regular around $(\bar x,0)$;
--   3. (H3) $\nabla\varphi$ is semismooth* at $(\bar x,0)$.
--
--   Then there is a neighbourhood $U$ of $\bar x$ such that Algorithm 5.3 is well-defined from every $x^0\in U$, and every sequence $(x^k)$ it generates from $x^0\in U$ converges Q-superlinearly to $\bar x$:
--   $$\lim_{k\to\infty}\frac{\|x^{k+1}-\bar x\|}{\|x^k-\bar x\|}=0.$$
--
--   This is the convergence theorem to which Theorem 6.6 reduces Algorithm 6.2.
--
--   **Formalization Note.** The conclusion holds for every run (every choice of Newton directions). "Q-superlinearly" is the $\varepsilon$-form: $x^k\to\bar x$ and eventually $\|x^{k+1}-\bar x\|\le\varepsilon\|x^k-\bar x\|$ for each $\varepsilon>0$; the ratio form is not used because a run that stops at $\bar x$ gives $0/0$. $\varphi$ is arbitrary away from $\bar x$; $C^{1,1}$ is assumed only on a neighbourhood. (H1)–(H3) are stated for the single-valued map $x\mapsto\{\nabla\varphi(x)\}$, so (H1) uses the coderivative $D^*\nabla\varphi(x)(d)=\partial^2\varphi(x)(d)$, while the algorithm's step (5.3) uses $\partial\langle d,\nabla\varphi\rangle(x)$; the two agree by the scalarization formula (2.11).
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 20, Theorem 5.7

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Alg53
open Filter Topology

namespace GenNewtonSubgrad.ProxReg

theorem theorem_5_7 {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (xbar : EuclideanSpace ℝ (Fin n))
    (hC11 : IsC11Around φ xbar) (hsol : gradient φ xbar = 0)
    (hH : StandingH (sv (gradient φ)) xbar 0) :
    ∃ U ∈ 𝓝 xbar, Alg53WellDefinedOn φ U ∧
      ∀ x : ℕ → EuclideanSpace ℝ (Fin n), IsAlg53Run φ x → x 0 ∈ U → IsQSuperlinear x xbar := by sorry

end GenNewtonSubgrad.ProxReg
