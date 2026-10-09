-- Prove2me | Theorems.Thm_GhadimiLan_RSG_eq_2_12
-- name    : GhadimiLan.RSG.eq_2_12
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-08T15:10:57.397796+00:00
-- url     : https://prove2.me/theorems/195573e9-9bfe-4ec9-ae82-b9cf4b1f3873
-- title:
--   (2.12), p. 7 — for convex f ∈ C^{1,1}_L with ∇f(x*) = 0, (1/L)‖∇f(y)‖² ≤ ⟨∇f(y), y − x*⟩
-- statement:
--   Let $f\in\mathcal C^{1,1}_L(\mathbb R^n)$ with $L>0$ be convex, and let $x^*$ satisfy $\nabla f(x^*)=0$. Then for every $y\in\mathbb R^n$,
--   $$\frac1L\|\nabla f(y)\|^2\le\langle\nabla f(y),\,y-x^*\rangle.$$
--
--   In the proof of Theorem 2.1 b) this is applied at the iterates $y=x_k$; it is the co-coercivity inequality (1.8) specialized to a stationary point, and it controls the gradient term in the distance recursion for $\|x_k-x^*\|^2$.
--
--   **Formalization Note** The paper writes the inequality at $x_k$; it holds for every point, and is stated so.
-- source:
--   Ghadimi & Lan, arXiv:1309.5549v1, proof of Theorem 2.1 b), Eq. (2.12), p. 7

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace GhadimiLan.RSG

/-- Eq. (2.12) (Ghadimi & Lan, arXiv:1309.5549v1, proof of Theorem 2.1 b), p. 7): for a convex
`f ∈ C^{1,1}_L(ℝⁿ)` (`L > 0`) with gradient map `g = ∇f` and a point `x*` with
`∇f(x*) = 0`, every `y` satisfies `(1/L)‖∇f(y)‖² ≤ ⟨∇f(y), y − x*⟩`. The paper states it at
the iterate `y = x_k`; the claim does not depend on how `y` was produced. -/
theorem eq_2_12 {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L) (hL : 0 < L)
    (hconv : ConvexOn ℝ Set.univ f) (xstar : E n) (hxstar : g xstar = 0) (y : E n) :
    1 / L * ‖g y‖ ^ 2 ≤ ⟪g y, y - xstar⟫_ℝ := by sorry

end GhadimiLan.RSG
