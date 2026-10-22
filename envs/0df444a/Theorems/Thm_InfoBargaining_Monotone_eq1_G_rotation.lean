-- Prove2me | Theorems.Thm_InfoBargaining_Monotone_eq1_G_rotation
-- name    : InfoBargaining.Monotone.eq1_G_rotation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:45.898863+00:00
-- url     : https://prove2.me/theorems/c2076040-0989-4791-a83c-483171c43ca6
-- title:
--   Display (1), p. 7 — G(v, α) increases in α for v < û and decreases in α for v > û
-- statement:
--   Let $F$ be the prior of the buyer's value, with mean $\hat u$, and let $G(v,\alpha)=F\big((v-(1-\alpha)\hat u)/\alpha\big)$ be the distribution function of the posterior mean $v=\alpha w+(1-\alpha)\hat u$ under the truth-or-noise signal of informativeness $\alpha$.
--
--   For all $\alpha,\alpha'\in(0,1)$ with $\alpha\le\alpha'$ and every $v\in\mathbb R$:
--   $$v<\hat u\ \Longrightarrow\ G(v,\alpha)\le G(v,\alpha'),\qquad v>\hat u\ \Longrightarrow\ G(v,\alpha')\le G(v,\alpha).$$
--
--   So the family $G(\cdot,\alpha)$ rotates about the prior mean $\hat u$: more information moves mass from the centre to both tails. This is the sign of the cross effect of the seller's cost on the buyer's marginal value of information.
--
--   **Formalization Note** This is display (1) in difference form. The paper states it with derivatives, $\partial G(v,\alpha)/\partial\alpha=-g(v,\alpha)(v-\hat u)/\alpha$, which is $>0$ for $v<\hat u$ and $<0$ for $v>\hat u$; that form needs a density, which the generalized prior of this mission does not have. Under the paper's density assumption the inequalities are strict and differential.
-- source:
--   Guo, Gathering Information before Negotiation, SSRN 3930651 (manuscript of 15 Feb 2022), p. 7, display (1)

import Mathlib
import Definitions.Def_InfoBargaining_Monotone_Setting

namespace InfoBargaining.Monotone

/-- Display (1), p. 7, in difference form: `G(v, α)` increases in `α` for `v < û` and
decreases in `α` for `v > û`, for `α` in `(0, 1)`. -/
theorem eq1_G_rotation (M : Model) {α α' : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hα' : α' ∈ Set.Ioo (0 : ℝ) 1) (hle : α ≤ α') (v : ℝ) :
    (v < M.uhat → M.G v α ≤ M.G v α') ∧ (M.uhat < v → M.G v α' ≤ M.G v α) := by sorry

end InfoBargaining.Monotone
