-- Prove2me | Theorems.Thm_NCPSeqOpt_AugLag_Supplement_theorem_3_1
-- name    : NCPSeqOpt.AugLag.Supplement.theorem_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T03:47:09.458186+00:00
-- url     : https://prove2.me/theorems/1fc300ea-8564-400f-a6df-d68a43a31e45
-- title:
--   Theorem 3.1, p. 6 — for (NLP), AGP of Definition 3.2 holds at a feasible point if and only if AGP as in (4) holds there
-- statement:
--   Consider the nonlinear program (NLP), that is, (NCP) with $\mathbb E=\mathbb R^m$ and $\mathcal K=\mathbb R^m_-=\{z\in\mathbb R^m:z_i\le0\ \forall i\}$: minimize $f(x)$ subject to $G(x)\le0$, where $f:\mathbb R^n\to\mathbb R$ and $G:\mathbb R^n\to\mathbb R^m$ are continuously differentiable. Let $\bar x$ be feasible, $G(\bar x)\le0$. For $x\in\mathbb R^n$ put
--   $$L(\Omega,x)=\{d\in\mathbb R^n:\ \min\{0,G_i(x)\}+\nabla G_i(x)^\top d\le0\ \text{for all } i \text{ with } G_i(\bar x)=0\}.$$
--   Then the following are equivalent:
--
--   1. AGP as in Definition 3.2 holds at $\bar x$: there are $x^k\to\bar x$ and $\Lambda^k\in\mathbb R^m_+$ with $\nabla f(x^k)+DG(x^k)^*\Lambda^k\to0$ and $\langle\Lambda^k,\Pi_{\mathbb R^m_-}(G(x^k))\rangle\to0$;
--   2. AGP as in (4) holds at $\bar x$: there is $x^k\to\bar x$ with
--   $$\big\|\Pi_{L(\Omega,x^k)}\big(-\nabla f(x^k)\big)\big\|\to0.$$
--
--   The theorem shows that the conic AGP condition of Definition 3.2, stated with multipliers, reduces in nonlinear programming to the multiplier-free AGP condition of Martínez and Svaiter, which justifies its name.
--
--   **Formalization Note** $\mathbb R^m_-$ is `negOrthant m` in `EuclideanSpace ℝ (Fin m)`, whose polar (the published `polarCone`) is $\mathbb R^m_+$. Definition 3.2 is the published `NCPSeqOpt.AugLag.IsAGP` unchanged. $\nabla G_i(x)^\top d$ is the $i$-th coordinate of $DG(x)d$.
--
--   Differences from the source:
--   - encoding: ∇G_i(x)ᵀd → the i-th coordinate of DG(x)d (`fderiv ℝ G x d i`); reason: equal for differentiable G, and G is C¹.
-- source:
--   Andreani, Gómez, Haeser, Mito & Ramos, On Optimality Conditions for Nonlinear Conic Programming, author's manuscript (revised 2021-04-20; Math. Oper. Res. doi:10.1287/moor.2021.1203), Theorem 3.1, p. 6 (with (NLP) and (4), p. 4, and Definition 3.2, p. 6)

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_NCPSeqOpt_AugLag_Setting
import Definitions.Def_StrictCQ_CAKKT_Setting
import Definitions.Def_NCPSeqOpt_AugLag_Supplement_Setting

namespace NCPSeqOpt.AugLag.Supplement

open MoreauProx.Decomposition NCPSeqOpt.AugLag
open scoped InnerProductSpace
open Filter Topology

theorem theorem_3_1 {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (hG : ContDiff ℝ 1 G)
    (xbar : EuclideanSpace ℝ (Fin n)) (hfeas : G xbar ∈ negOrthant m) :
    IsAGP f G (negOrthant m) xbar ↔ IsAGP4 f G xbar := by sorry

end NCPSeqOpt.AugLag.Supplement
