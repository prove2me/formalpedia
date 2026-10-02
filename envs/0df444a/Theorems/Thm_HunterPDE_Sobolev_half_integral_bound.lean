-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_half_integral_bound
-- name    : HunterPDE.Sobolev.half_integral_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T06:38:25.555515+00:00
-- url     : https://prove2.me/theorems/bdd14d6e-3685-447d-93d1-1cfdd900c8e7
-- title:
--   Lemma 3.26 — |∫_{−∞}^x g| ≤ ½∫|g| when ∫g = 0
-- statement:
--   Let $g : \mathbb{R} \to \mathbb{R}$ be an integrable function with compact support such that $\int g \, dt = 0$, and let $f(x) = \int_{-\infty}^x g(t)\, dt$. Then for every $x \in \mathbb{R}$
--   $$|f(x)| \le \frac{1}{2} \int |g| \, dt.$$
--
--   Applied to $g = \partial_i f(\cdot, x_i')$ for $f \in C_c^\infty(\mathbb{R}^n)$, it gives $|f(x)| \le \tfrac12 \int_{-\infty}^{\infty} |\partial_i f(t, x_i')|\, dt$, the pointwise estimate from which the Gagliardo–Nirenberg–Sobolev inequality is built.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 61, Lemma 3.26

import Mathlib

open MeasureTheory

namespace HunterPDE.Sobolev

/-- Lemma 3.26 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 61: if `g : ℝ → ℝ` is integrable
with compact support and `∫ g dt = 0`, then `f(x) = ∫_{-∞}^x g(t) dt` satisfies
`|f(x)| ≤ (1/2) ∫ |g| dt` for every `x`. -/
theorem half_integral_bound (g : ℝ → ℝ) (hg : Integrable g) (hgc : HasCompactSupport g)
    (hg0 : ∫ t, g t = 0) (x : ℝ) :
    |∫ t in Set.Iic x, g t| ≤ (1 / 2 : ℝ) * ∫ t, |g t| := by sorry

end HunterPDE.Sobolev
