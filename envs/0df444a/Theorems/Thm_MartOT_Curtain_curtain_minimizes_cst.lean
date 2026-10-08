-- Prove2me | Theorems.Thm_MartOT_Curtain_curtain_minimizes_cst
-- name    : MartOT.Curtain.curtain_minimizes_cst
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:21:27.591633+00:00
-- url     : https://prove2.me/theorems/a2672ae7-996e-4bef-a546-e90770820f75
-- title:
--   Proof of Theorem 4.21, p. 32 — π_lc minimizes every cost c_{s,t}(x, y) = 1_{]−∞,s]}(x)|y − t|
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathbb R$ with finite first moments and $\mu\preceq_C\nu$, and let $\pi_{\mathrm{lc}}$ be the left-curtain coupling. For real numbers $s,t$ consider the cost
--
--   $$c_{s,t}(x,y)=\mathbf 1_{]-\infty,s]}(x)\,|y-t| .$$
--
--   Then for every $s,t$, $\pi_{\mathrm{lc}}$ is an optimal martingale transport plan for $c_{s,t}$:
--
--   $$\pi_{\mathrm{lc}}\in\Pi_M(\mu,\nu)\quad\text{and}\quad\int c_{s,t}\,d\pi_{\mathrm{lc}}\le\int c_{s,t}\,d\pi\ \text{ for every }\pi\in\Pi_M(\mu,\nu).$$
--
--   So $\pi_{\mathrm{lc}}$ is simultaneously a minimizer of a two-parameter family of martingale transport problems. Combined with the variational lemma (Lemma 1.11) applied to $c_{s,t}$ for rational $s,t$, this yields the left-monotonicity of $\pi_{\mathrm{lc}}$.
--
--   **Formalization Note** Costs are compared in the extended reals ($c_{s,t}\ge0$, so the integrals lie in $[0,+\infty]$; they are finite since $\nu$ has a first moment). $\pi_{\mathrm{lc}}$ is any measure with the defining property of Theorem 4.18.
-- source:
--   arXiv:1208.1509v2, §4.4, proof of Theorem 4.21, p. 32 (first sentence)

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Curtain

open MeasureTheory

theorem curtain_minimizes_cst (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : MartOT.Var.ConvexLE μ ν) (πlc : Measure (ℝ × ℝ))
    (hlc : MartOT.Var.IsLeftCurtain μ ν πlc) (s t : ℝ) :
    MartOT.Var.IsOptimal (fun x y => (Set.Iic s).indicator (fun _ => (1 : ℝ)) x * |y - t|) μ ν πlc := by sorry

end MartOT.Curtain
