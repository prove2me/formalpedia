-- Prove2me | Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_5_4
-- name    : GenNewtonSubgrad.ProxReg.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:39.165122+00:00
-- url     : https://prove2.me/theorems/60bd307f-5572-4d59-9315-2c8dc576f883
-- title:
--   Lemma 5.4, p. 19 — coderivative characterization of metric regularity of a continuous map
-- statement:
--   Let $F:\mathbb R^n\to\mathbb R^m$ be continuous on a neighbourhood of $\bar x$. Then $F$ is metrically regular around $\bar x$ (that is, around $(\bar x,F(\bar x))$) if and only if there exist $c>0$ and a neighbourhood $U$ of $\bar x$ such that
--   $$\|v\|\ge c\|u\|\qquad\text{for all } v\in D^*F(x)(u),\ x\in U,\ u\in\mathbb R^m.\qquad(5.4)$$
--
--   Here $D^*F(x)(u)$ is the limiting coderivative of $F$ at $(x,F(x))$. The lemma is the form of the Mordukhovich criterion used to obtain the uniform estimate in the proof of Theorem 5.7.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 19, Lemma 5.4

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
open Filter Topology

namespace GenNewtonSubgrad.ProxReg

theorem lemma_5_4 {n m : ℕ} (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (xbar : EuclideanSpace ℝ (Fin n)) (hF : ∃ U ∈ 𝓝 xbar, ContinuousOn F U) :
    MetricRegularAround (sv F) xbar (F xbar) ↔
      ∃ c : ℝ, 0 < c ∧ ∃ U ∈ 𝓝 xbar, ∀ x ∈ U, ∀ u : EuclideanSpace ℝ (Fin m),
        ∀ v ∈ coderiv (sv F) x (F x) u, c * ‖u‖ ≤ ‖v‖ := by sorry

end GenNewtonSubgrad.ProxReg
