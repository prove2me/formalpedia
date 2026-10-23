-- Prove2me | Theorems.Thm_MoreauChance_Consistency_proposition_2_1_c
-- name    : MoreauChance.Consistency.proposition_2_1_c
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:22:28.498578+00:00
-- url     : https://prove2.me/theorems/5540f0e3-a1c2-476a-91a1-715cb1ca8583
-- title:
--   Proposition 2.1 c), p. 5 — lower epi-convergence: g(x) ≤ liminf e_{λk}g(xk) when xk ⇀ x, λk ↘ 0
-- statement:
--   Let $\mathcal H$ be a separable real Hilbert space and $g:\mathcal H\to\mathbb R$ convex and lower semicontinuous. Let $x_k\rightharpoonup x$ weakly in $\mathcal H$, and let $(\lambda_k)$ be a nonincreasing sequence of positive numbers with $\lambda_k\to0$ (that is, $\lambda_k\searrow0$). Then
--   $$
--   g(x)\le\liminf_{k\to\infty}\mathrm e_{\lambda_k}g(x_k).
--   $$
--
--   This is the "liminf" half of the epi-convergence of Moreau envelopes, in the weak topology. In the paper it is the step that passes from the values of the regularized problems back to the original objective.
--
--   **Formalization Note** The liminf is taken in the extended reals.
-- source:
--   van Ackooij, Pérez-Aros, Soto & Vilches, Inner Moreau envelope of nonsmooth conic chance constrained optimization problems, arXiv:2301.09803v1, p. 5, Proposition 2.1 c)

import Mathlib
import Definitions.Def_MoreauChance_Consistency_Basic

open Filter Topology
open scoped InnerProductSpace

namespace MoreauChance.Consistency

theorem proposition_2_1_c
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    (g : H → ℝ) (hg_convex : ConvexOn ℝ Set.univ g) (hg_lsc : LowerSemicontinuous g)
    (xk : ℕ → H) (x : H) (lamk : ℕ → ℝ) (hxk : WeakConv xk x) (hlam_pos : ∀ k, 0 < lamk k)
    (hlam_anti : Antitone lamk) (hlam_lim : Tendsto lamk atTop (𝓝 0)) :
    (g x : EReal) ≤
      Filter.liminf (fun k => moreauEnv (fun z => (g z : EReal)) (lamk k) (xk k)) atTop := by sorry

end MoreauChance.Consistency
