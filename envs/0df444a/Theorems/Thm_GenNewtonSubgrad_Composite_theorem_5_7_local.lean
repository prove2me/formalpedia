-- Prove2me | Theorems.Thm_GenNewtonSubgrad_Composite_theorem_5_7_local
-- name    : GenNewtonSubgrad.Composite.theorem_5_7_local
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-23T16:33:55.828082+00:00
-- url     : https://prove2.me/theorems/586bfb45-4505-4576-9eb4-085953982e5c
-- title:
--   Theorem 5.7 (localized form) — iterates of Algorithm 5.3 stay near $\bar x$ and converge Q-superlinearly
-- statement:
--   This is Theorem 5.7 of Khanh–Mordukhovich–Phat in the localized form that its proof establishes: the iterates of the generalized Newton method stay in any prescribed neighbourhood of the solution when started close enough to it.
--
--   Let $\varphi:\mathbb R^n\to\mathbb R$ be of class $C^{1,1}$ around $\bar x$, with $\nabla\varphi(\bar x)=0$, and assume the standing assumptions (H1)–(H3) for the gradient mapping $\nabla\varphi$ at $(\bar x,0)$:
--
--   1. (H1) there are neighbourhoods $U$ of $\bar x$ and $V$ of $0$ such that for every $x\in U$ with $\nabla\varphi(x)\in V$ some direction $d$ satisfies $-\nabla\varphi(x)\in(D^*\nabla\varphi)(x)(d)$;
--   2. (H2) $\nabla\varphi$ is metrically regular around $(\bar x,0)$;
--   3. (H3) $\nabla\varphi$ is semismooth\* at $(\bar x,0)$.
--
--   A step $x\mapsto x'$ of Algorithm 5.3 is: $x'=x$ if $\nabla\varphi(x)=0$, and otherwise $d=x'-x$ solves the Newton inclusion
--   $$-\nabla\varphi(x)\in\partial\langle d,\nabla\varphi\rangle(x).\tag{5.3}$$
--
--   Then for every neighbourhood $V$ of $\bar x$ there is a neighbourhood $U$ of $\bar x$ such that:
--
--   1. every finite run $x^0,\dots,x^N$ of Algorithm 5.3 with $x^0\in U$ satisfies $x^N\in V$, and it can be continued, i.e. some step $x^N\mapsto x^{N+1}$ of Algorithm 5.3 exists;
--   2. every infinite run $\{x^k\}$ of Algorithm 5.3 with $x^0\in U$ converges Q-superlinearly to $\bar x$:
--   $$x^k\to\bar x\quad\text{and}\quad\lim_{k\to\infty}\frac{\|x^{k+1}-\bar x\|}{\|x^k-\bar x\|}=0 .$$
--
--   Taking $V=\mathbb R^n$ gives Theorem 5.7 itself. The localization is what the proof of Theorem 5.7 actually shows (the iterates contract towards $\bar x$ inside a small ball, following Klatte–Kummer, Theorem 10.7), and it is what is needed to apply Theorem 5.7 to a function such as the forward–backward envelope $\varphi_\gamma$ of Section 7, whose good properties (and the identification of Algorithm 7.6 with Algorithm 5.3, Remark 7.7) are only available on a neighbourhood of $\bar x$; this is how the proof of Theorem 7.8 applies Theorem 5.7.
--
--   **Formalization Note** $(D^*\nabla\varphi)(x)$ is the limiting coderivative of the single-valued map $\nabla\varphi$. Q-superlinear convergence is stated in $\varepsilon$-form (for every $\varepsilon>0$, eventually $\|x^{k+1}-\bar x\|\le\varepsilon\|x^k-\bar x\|$). A finite run is a sequence whose first $N$ consecutive pairs are steps of Algorithm 5.3; well-definedness is the continuation property in item 1, exactly as in `Alg53WellDefinedOn`.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 20, Theorem 5.7 and its proof (localization of the iterates used in the proof of Theorem 7.8, p. 36-37)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Alg53

open Filter Topology
open scoped InnerProductSpace

namespace GenNewtonSubgrad.Composite

theorem theorem_5_7_local {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (xbar : EuclideanSpace ℝ (Fin n))
    (hC11 : GenNewtonSubgrad.ProxReg.IsC11Around φ xbar) (hsol : gradient φ xbar = 0)
    (hH : GenNewtonSubgrad.ProxReg.StandingH (GenNewtonSubgrad.ProxReg.sv (gradient φ)) xbar 0) :
    ∀ V ∈ 𝓝 xbar, ∃ U ∈ 𝓝 xbar,
      (∀ (N : ℕ) (x : ℕ → EuclideanSpace ℝ (Fin n)), x 0 ∈ U →
        (∀ k < N, GenNewtonSubgrad.ProxReg.alg53Step φ (x k) (x (k + 1))) →
          x N ∈ V ∧ ∃ x', GenNewtonSubgrad.ProxReg.alg53Step φ (x N) x') ∧
      ∀ x : ℕ → EuclideanSpace ℝ (Fin n), GenNewtonSubgrad.ProxReg.IsAlg53Run φ x → x 0 ∈ U →
        GenNewtonSubgrad.ProxReg.IsQSuperlinear x xbar := by sorry

end GenNewtonSubgrad.Composite
