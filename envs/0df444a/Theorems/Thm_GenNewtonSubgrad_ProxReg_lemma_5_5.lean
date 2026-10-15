-- Prove2me | Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_5_5
-- name    : GenNewtonSubgrad.ProxReg.lemma_5_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:42.040039+00:00
-- url     : https://prove2.me/theorems/491e5994-52e5-4e06-a98b-275728b61ac0
-- title:
--   Lemma 5.5, p. 19 — semismoothness* of a Lipschitz gradient as an $o(\|x-\bar x\|)$ estimate
-- statement:
--   Let $\varphi:\mathbb R^n\to\mathbb R$ be of class $C^{1,1}$ around $\bar x$. Then the gradient mapping $\nabla\varphi$ is semismooth* at $(\bar x,\nabla\varphi(\bar x))$ if and only if
--   $$\nabla\varphi(x)-\nabla\varphi(\bar x)-\partial^2\varphi(x)(x-\bar x)\subseteq o(\|x-\bar x\|),$$
--   that is, for every $\varepsilon>0$ there is $\delta>0$ such that
--   $$\|\nabla\varphi(x)-\nabla\varphi(\bar x)-v\|\le\varepsilon\|x-\bar x\|\qquad\text{for all } v\in\partial^2\varphi(x)(x-\bar x),\ x\in\mathbb B_\delta(\bar x).$$
--   Here $\partial^2\varphi(x)(u)=(D^*\nabla\varphi)(x)(u)$ and $\mathbb B_\delta(\bar x)$ is the closed ball.
--
--   This is how (H3) enters the convergence estimate of Theorem 5.7.
--
--   **Formalization Note.** The second form ("which means …") is the one formalized. For $C^{1,1}$ functions $\partial^2\varphi(x)(u)$ is read as the coderivative of the single-valued gradient map at $(x,\nabla\varphi(x))$, as on p. 19.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 19, Lemma 5.5

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
open Filter Topology

namespace GenNewtonSubgrad.ProxReg

theorem lemma_5_5 {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℝ) (xbar : EuclideanSpace ℝ (Fin n))
    (hφ : IsC11Around φ xbar) :
    IsSemismoothStar (sv (gradient φ)) xbar (gradient φ xbar) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Metric.closedBall xbar δ,
        ∀ v ∈ coderiv (sv (gradient φ)) x (gradient φ x) (x - xbar),
          ‖gradient φ x - gradient φ xbar - v‖ ≤ ε * ‖x - xbar‖ := by sorry

end GenNewtonSubgrad.ProxReg
