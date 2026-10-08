-- Prove2me | Theorems.Thm_MartOT_Curtain_theorem_1_8
-- name    : MartOT.Curtain.theorem_1_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:19:26.142892+00:00
-- url     : https://prove2.me/theorems/a04b910b-80ba-424c-be93-32b3b58d82ab
-- title:
--   Theorem 1.8, p. 7 — for every t, ν_t^{π_lc} is the ⪯C-least element of {ν_t^π : π ∈ Π_M(µ, ν)}
-- statement:
--   Let $\mu,\nu$ be probability measures on $\mathbb R$ with finite first moments and $\mu\preceq_C\nu$, and let $\pi_{\mathrm{lc}}$ be the left-curtain coupling. For a plan $\pi$ and $t\in\mathbb R$ write
--
--   $$\nu^\pi_t=\operatorname{proj}^y_\#\big(\pi|_{]-\infty,t]\times\mathbb R}\big)$$
--
--   for the image of the mass $\mu|_{]-\infty,t]}$ under $\pi$. Then for every real $t$ and every martingale transport plan $\pi\in\Pi_M(\mu,\nu)$,
--
--   $$\nu^{\pi_{\mathrm{lc}}}_t\preceq_C\nu^\pi_t .$$
--
--   That is, $\pi_{\mathrm{lc}}$ is canonical for the convex order in the same way as the Hoeffding–Fréchet coupling is canonical for first-order stochastic dominance: at every level $t$ it sends the left part of $\mu$ to the least spread-out target possible.
--
--   **Formalization Note** The page says $\nu^{\pi_{\mathrm{lc}}}_t$ is "minimal" in the family $\{\nu^\pi_t:\pi\in\Pi_M(\mu,\nu)\}$; it is formalized as the *least* element (below every member of the family), which is how the paper uses it in the proof of Theorem 4.21 (p. 32) and restates it in Theorem 1.9. $\pi_{\mathrm{lc}}$ is any measure with the defining property of Theorem 4.18 (`IsLeftCurtain`).
-- source:
--   arXiv:1208.1509v2, Theorem 1.8, p. 7

import Mathlib
import Definitions.Def_MartOT_Var_Setting

namespace MartOT.Curtain

open MeasureTheory

theorem theorem_1_8 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (πlc : Measure (ℝ × ℝ)) (hlc : MartOT.Var.IsLeftCurtain μ ν πlc) (t : ℝ) :
    ∀ π : Measure (ℝ × ℝ), MartOT.Var.IsMartingalePlan μ ν π →
      MartOT.Var.ConvexLE (MartOT.Var.targetUpTo πlc t) (MartOT.Var.targetUpTo π t) := by sorry

end MartOT.Curtain
