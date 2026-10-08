-- Prove2me | Theorems.Thm_MartOT_Curtain_theorem_4_21
-- name    : MartOT.Curtain.theorem_4_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:49.908089+00:00
-- url     : https://prove2.me/theorems/fc24fdae-6db2-4373-ac6b-064a8e1ece55
-- title:
--   Theorem 4.21, p. 32 — the left-curtain coupling π_lc is left-monotone (Definition 1.4)
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathbb R$ with finite first moments and $\mu\preceq_C\nu$, and let $\pi_{\mathrm{lc}}$ be the left-curtain coupling of Theorem 4.18. Then $\pi_{\mathrm{lc}}$ is **left-monotone**: there is a Borel set $\Gamma\subseteq\mathbb R^2$ with $\pi_{\mathrm{lc}}(\mathbb R^2\setminus\Gamma)=0$ such that no three points $(x,y^-),(x,y^+),(x',y')\in\Gamma$ satisfy
--
--   $$x<x'\quad\text{and}\quad y^-<y'<y^+ .$$
--
--   Together with Theorem 4.18 this gives the existence half of Theorem 1.5: a left-monotone martingale transport plan exists between any two probability measures in convex order.
--
--   **Formalization Note** $\pi_{\mathrm{lc}}$ is any measure with the defining property of Theorem 4.18 (`IsLeftCurtain`); that it is a martingale plan is part of Theorem 4.18. "$\pi(\Gamma)=1$" is written as $\pi(\Gamma^c)=0$.
-- source:
--   arXiv:1208.1509v2, Theorem 4.21, p. 32

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Curtain

open MeasureTheory

theorem theorem_4_21 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (πlc : Measure (ℝ × ℝ)) (hlc : MartOT.Var.IsLeftCurtain μ ν πlc) :
    MartOT.Var.IsLeftMonotone πlc := by sorry

end MartOT.Curtain
