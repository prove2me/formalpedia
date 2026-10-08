-- Prove2me | Theorems.Thm_MartOT_Curtain_theorem_1_5
-- name    : MartOT.Curtain.theorem_1_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:20:28.934549+00:00
-- url     : https://prove2.me/theorems/330cdc4c-305b-4452-a0cd-f545d853ca6f
-- title:
--   Theorem 1.5, p. 6 — for µ ⪯C ν in P there is exactly one left-monotone plan in Π_M(µ, ν)
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathbb R$ with finite first moments that are in convex order, $\mu\preceq_C\nu$ (that is, $\int\varphi\,d\mu\le\int\varphi\,d\nu$ for every convex $\varphi:\mathbb R\to\mathbb R$). Then there exists exactly one martingale transport plan $\pi\in\Pi_M(\mu,\nu)$ that is **left-monotone**: there is a Borel set $\Gamma\subseteq\mathbb R^2$ with $\pi(\Gamma)=1$ such that no three points $(x,y^-),(x,y^+),(x',y')\in\Gamma$ satisfy
--
--   $$x<x'\quad\text{and}\quad y^-<y'<y^+ .$$
--
--   This plan is the **left-curtain coupling** $\pi_{\mathrm{lc}}$. It is the martingale analogue of the monotone (Hoeffding–Fréchet) coupling of classical optimal transport, and it is the coupling that the later results of the paper identify as the optimizer of the martingale transport problem for several families of costs.
--
--   **Formalization Note** $\Pi_M(\mu,\nu)$ is encoded through the paper's characterization (4): marginals $\mu$, $\nu$ and $\int\rho(x)(y-x)\,d\pi=0$ for every bounded Borel $\rho$. $\pi(\Gamma)=1$ is written $\pi(\Gamma^c)=0$. Uniqueness is among all measures on $\mathbb R^2$ (any element of $\Pi_M(\mu,\nu)$ is a probability measure).
-- source:
--   arXiv:1208.1509v2, Theorem 1.5, p. 6 (proof: Theorems 4.18, 4.21, 5.3)

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Curtain

open MeasureTheory

theorem theorem_1_5 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) :
    ∃! π : Measure (ℝ × ℝ), MartOT.Var.IsMartingalePlan μ ν π ∧ MartOT.Var.IsLeftMonotone π := by sorry

end MartOT.Curtain
