-- Prove2me | Theorems.Thm_OneStepProx_minimizer_mem_scaledProx
-- name    : OneStepProx.minimizer_mem_scaledProx
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:24.307009+00:00
-- url     : https://prove2.me/theorems/0bc5de3e-3105-4264-a4bd-a0902d4b644c
-- title:
--   §1.2, p.5 — a minimizer of $g+h$ is a fixed point of scaled proximal gradient descent
-- statement:
--   Let $g:\mathbb R^d\to\mathbb R$ be differentiable at $x^*$, let $h:\mathbb R^d\to\mathbb R\cup\{\infty\}$ be proper and convex, and suppose $x^*$ minimizes $g+h$. Then for every positive definite $C$,
--
--   $$
--   x^*\in\operatorname{prox}^C_h\bigl(x^*-C^{-1}\nabla g(x^*)\bigr).
--   $$
--
--   The function $g$ need not be convex. This is what makes the second term of the proof's triangle inequality vanish.
--
--   Differences from the source:
--   - reading: p.5 states $x^*\in\operatorname{prox}^\lambda_h(x^*-\lambda\nabla g(x^*))$ for a step length $\lambda$ → the scaled form for every $C\succ0$; reason: the proof of Theorem 2.1, p.7, invokes the scaled form ("Recall from section 1.2 that $\hat\theta$ is a fixed point of scaled proximal gradient descent"), and $C=\lambda^{-1}I$ gives the printed form.
--   - generalization: $g$ closed and continuously differentiable → $g$ differentiable at $x^*$; reason: the argument uses only the derivative at $x^*$, and a $C^1$ function satisfies this.
--   - encoding: $\min_{x\in\mathbb R^d}g(x)+h(x)$ with $h$ extended-valued → $x^*\in D$ and $g(x^*)+h(x^*)\le g(w)+h(w)$ for $w\in D$; reason: the value is $+\infty$ off $D$, and $D$ is nonempty.
-- source:
--   Bassett & Deride, One-Step Estimation with Scaled Proximal Methods, arXiv:2004.14521v3, §1.2, p.5, "Hence we conclude that x* ∈ prox^λ_h (x* − λ∇g(x*))"; proof of Theorem 2.1, p.7, "Recall from section 1.2 that θ̂ is a fixed point of scaled proximal gradient descent"

import Mathlib
import Definitions.Def_OneStepProx_IsProperConvex
import Definitions.Def_OneStepProx_scaledProx

namespace OneStepProx

/-- Bassett & Deride, arXiv:2004.14521v3, §1.2, p.5, in the scaled form invoked in the proof of
Theorem 2.1, p.7 ("Recall from section 1.2 that θ̂ is a fixed point of scaled proximal gradient
descent"): if `g` is differentiable at `xstar`, `h` is proper convex and `xstar` minimizes `g + h`,
then `xstar ∈ prox^C_h(xstar − C⁻¹∇g(xstar))` for every `C ≻ 0`.

**Formalization Note.** `g + h` has value `+∞` off `D`, so a minimizer lies in `D` and it suffices
to compare with the points of `D`. The convexity of `g` is not assumed: the paper's p.8 notes
that `gₙ` need not be convex. -/
theorem minimizer_mem_scaledProx {d : ℕ} {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef)
    {g : EuclideanSpace ℝ (Fin d) → ℝ} {D : Set (EuclideanSpace ℝ (Fin d))}
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hh : IsProperConvex D h)
    {xstar : EuclideanSpace ℝ (Fin d)} (hg : DifferentiableAt ℝ g xstar) (hx : xstar ∈ D)
    (hmin : ∀ w ∈ D, g xstar + h xstar ≤ g w + h w) :
    xstar ∈ scaledProx C D h (xstar - Matrix.toEuclideanLin C⁻¹ (gradient g xstar)) := by sorry

end OneStepProx
