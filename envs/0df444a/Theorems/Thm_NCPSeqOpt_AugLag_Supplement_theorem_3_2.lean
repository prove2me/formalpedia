-- Prove2me | Theorems.Thm_NCPSeqOpt_AugLag_Supplement_theorem_3_2
-- name    : NCPSeqOpt.AugLag.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T03:49:09.959097+00:00
-- url     : https://prove2.me/theorems/ad0742c2-6c03-45a0-8011-9cbf9e5d2bdf
-- title:
--   Theorem 3.2, p. 7 — every local minimizer of (NCP) satisfies CAKKT, with no constraint qualification
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ and $G:\mathbb R^n\to\mathbb E$ be continuously differentiable, $\mathbb E$ a finite-dimensional real inner product space and $\mathcal K\subseteq\mathbb E$ a nonempty closed convex cone. Suppose $\bar x$ is a local minimizer of
--   $$\min_{x} f(x)\quad\text{subject to}\quad G(x)\in\mathcal K,$$
--   that is, $G(\bar x)\in\mathcal K$ and for some $\delta>0$, $f(\bar x)\le f(x)$ for every $x$ with $G(x)\in\mathcal K$ and $\|x-\bar x\|\le\delta$. Then $\bar x$ satisfies CAKKT (Definition 3.3): there are sequences $x^k\to\bar x$ and $\Lambda^k\in\mathcal K^\circ$ such that
--   $$\nabla f(x^k)+DG(x^k)^*\Lambda^k\to0,\qquad\langle\Lambda^k,\Pi_{\mathcal K}(G(x^k))\rangle\to0,\qquad\langle\Lambda^k,\Pi_{\mathcal K^\circ}(G(x^k))\rangle\to0.$$
--
--   No constraint qualification is assumed: CAKKT is a genuine necessary optimality condition for (NCP), and hence so are the weaker conditions AGP and TAKKT.
--
--   **Formalization Note** CAKKT is the published `NCPSeqOpt.AugLag.IsCAKKT`, with all three limits on one pair of sequences. "Local minimizer" is stated with a closed ball, as in the proof on p. 7; it is equivalent to minimality on $\Omega\cap U$ for a neighbourhood $U$ of $\bar x$.
--
--   Differences from the source:
--   - encoding: "local minimizer of (NCP)" → f(x̄) ≤ f(x) for feasible x in a closed ball B[x̄, δ], δ > 0; reason: equivalent to the neighbourhood definition; the proof on p. 7 uses this form.
-- source:
--   Andreani, Gómez, Haeser, Mito & Ramos, On Optimality Conditions for Nonlinear Conic Programming, author's manuscript (revised 2021-04-20; Math. Oper. Res. doi:10.1287/moor.2021.1203), Theorem 3.2, p. 7 (Definition 3.3, p. 7)

import Mathlib
import Definitions.Def_MoreauProx_Decomposition_Cones
import Definitions.Def_NCPSeqOpt_AugLag_Setting
import Definitions.Def_StrictCQ_CAKKT_Setting
import Definitions.Def_NCPSeqOpt_AugLag_Supplement_Setting

namespace NCPSeqOpt.AugLag.Supplement

open MoreauProx.Decomposition NCPSeqOpt.AugLag
open scoped InnerProductSpace
open Filter Topology

theorem theorem_3_2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (G : EuclideanSpace ℝ (Fin n) → E) (hG : ContDiff ℝ 1 G)
    (K : Set E) (hK : IsClosedConvexCone K)
    (xbar : EuclideanSpace ℝ (Fin n)) (hmin : IsLocalMinNCP f G K xbar) :
    IsCAKKT f G K xbar := by sorry

end NCPSeqOpt.AugLag.Supplement
