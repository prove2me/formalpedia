-- Prove2me | Theorems.Thm_GenNewtonSubgrad_ProxReg_scalarization_2_11
-- name    : GenNewtonSubgrad.ProxReg.scalarization_2_11
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-23T16:40:37.937997+00:00
-- url     : https://prove2.me/theorems/8a8b27d1-28fb-4ce4-ae6d-051c5f7d49d8
-- title:
--   Coderivative scalarization (2.11): $D^*F(\bar x)(v)=\partial\langle v,F\rangle(\bar x)$ for locally Lipschitz $F$
-- statement:
--   This is the coderivative scalarization formula (2.11).
--
--   Let $F:\mathbb R^n\to\mathbb R^m$ be Lipschitz continuous on a neighbourhood of $\bar x$. Write $D^*F(\bar x)$ for the limiting (Mordukhovich) coderivative of $F$ at $\bar x$, i.e. $u\in D^*F(\bar x)(v)$ iff $(u,-v)$ lies in the limiting normal cone to $\operatorname{gph}F$ at $(\bar x,F(\bar x))$, and write $\partial$ for the limiting subdifferential. Then for every $v\in\mathbb R^m$
--   $$D^*F(\bar x)(v)=\partial\langle v,F\rangle(\bar x),$$
--   where $\langle v,F\rangle$ denotes the real-valued function $x\mapsto\langle v,F(x)\rangle$.
--
--   The formula reduces the coderivative of a Lipschitz single-valued map to first-order subgradients of scalar functions. In the generalized Newton method it identifies the Newton inclusion (5.3), $-\nabla\varphi(x)\in\partial\langle d,\nabla\varphi\rangle(x)$, with $-\nabla\varphi(x)\in\partial^2\varphi(x)(d)=(D^*\nabla\varphi)(x)(d)$, and it is the first step in the proof of Lemma 5.6.
--
--   **Formalization Note** Lipschitz continuity around $\bar x$ is stated as Lipschitz continuity on some neighbourhood of $\bar x$. The scalar function is regarded as extended-real-valued (it is finite everywhere) so that the platform's limiting subdifferential applies.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 7, formula (2.11); see Mordukhovich, Variational Analysis and Generalized Differentiation I (2006), Theorem 1.90

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis

open Filter Topology
open scoped InnerProductSpace

namespace GenNewtonSubgrad.ProxReg

theorem scalarization_2_11 {n m : ℕ}
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (xbar : EuclideanSpace ℝ (Fin n))
    (hF : ∃ U ∈ 𝓝 xbar, ∃ L, LipschitzOnWith L F U) (v : EuclideanSpace ℝ (Fin m)) :
    coderiv (sv F) xbar (F xbar) v =
      NonconvexSplitting.Shared.LimitingSubdiff (fun z => ((⟪v, F z⟫_ℝ : ℝ) : EReal)) xbar := by
  sorry

end GenNewtonSubgrad.ProxReg
