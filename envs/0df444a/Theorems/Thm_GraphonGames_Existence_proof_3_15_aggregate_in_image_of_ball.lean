-- Prove2me | Theorems.Thm_GraphonGames_Existence_proof_3_15_aggregate_in_image_of_ball
-- name    : GraphonGames.Existence.proof_3_15_aggregate_in_image_of_ball
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:38.048161+00:00
-- url     : https://prove2.me/theorems/7cc6e7f0-801e-415e-b575-69b3d735d232
-- title:
--   Proof of Theorem 3.15, p. 15 — Zα ∈ W(B_χ) with χ = c₀
-- statement:
--   Let $w$ be a graphon with operator $\mathbf W$, let $b,\mu_0$ satisfy Assumption 1, let $b$ satisfy Assumption 5 with bound $c_0$, and assume $\sqrt{c_z}\|\mathbf W\|<1$. Put $\chi=c_0$ and let $B_\chi=\{g\in L^2(I):\|g\|\le\chi\}$ be the closed ball. For every $\alpha\in L^2(I)$, its aggregate lies in the image of the ball:
--   $$\mathbf Z\alpha\in\mathbf W(B_\chi),$$
--   that is, there is $g\in L^2(I)$ with $\|g\|_{L^2(I)}\le c_0$ and $\mathbf Z\alpha=\mathbf Wg$ almost everywhere.
--
--   This is the first claim of the proof of Theorem 3.15: all aggregates lie in one fixed set, independent of $\alpha$.
-- source:
--   Carmona, Cooney, Graves & Laurière, Stochastic Graphon Games: I. The Static Case, arXiv:1911.10664v1, p. 15, proof of Theorem 3.15, first and second sentences (via Remark 3.3, (7), p. 9)

import Mathlib
import Definitions.Def_GraphonGames_Existence_Setting

open MeasureTheory
open scoped ENNReal

namespace GraphonGames.Existence

theorem proof_3_15_aggregate_in_image_of_ball (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz c0 : ℝ)
    (h1 : Asm1 b μ0 cα cz) (h5 : Asm5 b c0) (w : I → I → ℝ) (hw : IsGraphon w)
    (hW : Real.sqrt cz * (opNorm w).toReal < 1) (α : I → ℝ) (hα : MemLp α 2 volume)
    (z : I → ℝ) (hz : IsAggregate w b α z) :
    ∃ g : I → ℝ, MemLp g 2 volume ∧ eLpNorm g 2 volume ≤ ENNReal.ofReal c0 ∧
      z =ᵐ[volume] graphonApply w g := by sorry

end GraphonGames.Existence
