-- Prove2me | Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_5_6
-- name    : GenNewtonSubgrad.ProxReg.lemma_5_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:42.234736+00:00
-- url     : https://prove2.me/theorems/a75572c1-7453-4717-87bc-751907e54bea
-- title:
--   Lemma 5.6, p. 20 — subadditivity of the coderivative of a locally Lipschitz map
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R^m$ be Lipschitz continuous on a neighbourhood of $\bar x$. Then for all $u_1,u_2\in\mathbb R^m$,
--   $$D^*F(\bar x)(u_1+u_2)\subseteq D^*F(\bar x)(u_1)+D^*F(\bar x)(u_2),\qquad(5.6)$$
--   where the right-hand side is the Minkowski sum of sets and $D^*F(\bar x)$ is the limiting coderivative at $(\bar x,F(\bar x))$.
--
--   The lemma is used in the proof of Theorem 5.7 to split a second-order subdifferential along a sum of directions.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 20, Lemma 5.6

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
open Filter Topology
open scoped Pointwise

namespace GenNewtonSubgrad.ProxReg

theorem lemma_5_6 {n m : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (xbar : EuclideanSpace ℝ (Fin n)) (hF : ∃ U ∈ 𝓝 xbar, ∃ L, LipschitzOnWith L F U)
    (u₁ u₂ : EuclideanSpace ℝ (Fin m)) :
    coderiv (sv F) xbar (F xbar) (u₁ + u₂) ⊆
      coderiv (sv F) xbar (F xbar) u₁ + coderiv (sv F) xbar (F xbar) u₂ := by sorry

end GenNewtonSubgrad.ProxReg
