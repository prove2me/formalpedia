-- Prove2me | Theorems.Thm_MartOT_Abs_theorem_2_6_necessity
-- name    : MartOT.Abs.theorem_2_6_necessity
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-05T04:54:48.28636+00:00
-- url     : https://prove2.me/theorems/07a54b21-02d9-461c-bb0e-053f69e41ef9
-- title:
--   Theorem 2.6, p. 12 (necessity) — a martingale transport plan in Π_M(µ, ν) forces µ ⪯C ν (Jensen)
-- statement:
--   Let $\mu,\nu\in\mathcal M$, i.e. finite measures on $\mathbb R$ with finite first moment. If there exists a martingale transport plan $\pi\in\Pi_M(\mu,\nu)$, then $\mu\preceq_C\nu$: for every convex $\varphi:\mathbb R\to\mathbb R$,
--
--   $$\int\varphi\,d\mu\le\int\varphi\,d\nu .$$
--
--   This is the necessity half of Theorem 2.6 of the paper, which it derives from Jensen's inequality: $\int\varphi(y)\,d\nu(y)=\iint\varphi(y)\,d\pi_x(y)\,d\mu(x)\ge\int\varphi(x)\,d\mu(x)$.
--
--   **Formalization Note** $\Pi_M(\mu,\nu)$ is `IsMartingalePlan` (marginals $\mu,\nu$ and $\int\rho(x)(y-x)\,d\pi=0$ for all bounded Borel $\rho$, the paper's (4)); $\preceq_C$ is `ConvexLE` (Definition 2.1), whose integrals $\int\varphi\,d\mu\in[-\infty,+\infty]$ are computed as $\int\varphi^+-\int\varphi^-$ in `EReal`. The measures need not be probability measures, as in the paper's class $\mathcal M$.
-- source:
--   arXiv:1208.1509v2 (Beiglböck–Juillet, On a problem of optimal transport under marginal martingale constraints), Theorem 2.6, p. 12 — necessity, proved on p. 12 by Jensen's inequality

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Abs

open MeasureTheory

theorem theorem_2_6_necessity (μ ν : Measure ℝ) (hμ : MartOT.Var.InM μ) (hν : MartOT.Var.InM ν)
    (π : Measure (ℝ × ℝ)) (hπ : MartOT.Var.IsMartingalePlan μ ν π) :
    MartOT.Var.ConvexLE μ ν := by sorry

end MartOT.Abs
