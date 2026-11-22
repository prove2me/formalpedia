-- Prove2me | Theorems.Thm_KarimiPL_Rel_grad_sqrt_gap_ge
-- name    : KarimiPL.Rel.grad_sqrt_gap_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:44:14.30141+00:00
-- url     : https://prove2.me/theorems/64a2cabf-1a5a-4480-a5ff-c0972a5f3ac6
-- title:
--   (20), p. 13 — under PL, g = √(f − f*) has ‖∇g(x)‖ ≥ √(μ/2) at every x ∉ X*
-- statement:
--   Let $f:\mathbb R^d\to\mathbb R$ be differentiable, let $x^*$ be a global minimizer, $f^*=f(x^*)$, and let $\mathcal X^*$ be the set of global minimizers. Suppose $f$ satisfies the Polyak–Łojasiewicz inequality with constant $\mu>0$: $\frac12\|\nabla f(x)\|^2\ge\mu(f(x)-f^*)$ for all $x$. Define
--   $$g(x)=\sqrt{f(x)-f^*}.$$
--   Then for every $x\notin\mathcal X^*$,
--   $$\|\nabla g(x)\|\ge\sqrt{\frac\mu2}.$$
--
--   This gradient lower bound for the square root of the optimality gap is the key estimate in the paper's proof that PL implies quadratic growth.
--
--   **Formalization Note** At $x\notin\mathcal X^*$ one has $f(x)>f^*$, so $g$ is differentiable there; the gradient is Mathlib's `gradient` of `fun y => Real.sqrt (f y - f x*)`. The paper's standing Lipschitz-gradient assumption is not used by this step and is omitted.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, Appendix A, bullet "PL → QG", display (20), p. 13

import Mathlib
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_KarimiPL_Rel_Conditions

namespace KarimiPL.Rel

theorem grad_sqrt_gap_ge {d : ℕ} (f : E d → ℝ) (hdiff : Differentiable ℝ f)
    (xstar : E d) (hxstar : ∀ y, f xstar ≤ f y)
    (μ : ℝ) (hμ : 0 < μ) (hPL : ShiOptRates.PolyakLojasiewicz f (gradient f) μ (f xstar))
    (x : E d) (hx : x ∉ solSet f) :
    Real.sqrt (μ / 2) ≤ ‖gradient (fun y => Real.sqrt (f y - f xstar)) x‖ := by sorry

end KarimiPL.Rel
