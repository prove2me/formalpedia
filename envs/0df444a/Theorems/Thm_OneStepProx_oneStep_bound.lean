-- Prove2me | Theorems.Thm_OneStepProx_oneStep_bound
-- name    : OneStepProx.oneStep_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:31.719637+00:00
-- url     : https://prove2.me/theorems/0e6a8697-1cc6-4479-85e9-f1628a9cd420
-- title:
--   (2.3), p.7 — the deterministic one-step bound
-- statement:
--   Let $C\succ0$ and $H$ be $d\times d$ matrices, let $h:\mathbb R^d\to\mathbb R\cup\{\infty\}$ be proper and convex, let $g$ be differentiable at $a$ and $b$, and let $p_a\in\operatorname{prox}^C_h(a-C^{-1}\nabla g(a))$, $p_b\in\operatorname{prox}^C_h(b-C^{-1}\nabla g(b))$. With $K=\sqrt{\lambda_{\max}(C)/\lambda_{\min}(C)}$,
--
--   $$
--   \|p_a-p_b\|\le K\,\|I-C^{-1}H\|\,\|a-b\|+K\,\|C^{-1}\|\,\bigl\|\nabla g(a)-\nabla g(b)-H(a-b)\bigr\| .
--   $$
--
--   Applied with $a=\hat\theta_{init}$, $b=\hat\theta$, $C=C_n$, $g=g_n$ and multiplied by $\sqrt n$, this is the estimate (2.3), whose terms vanish by assumptions (i), (ii) and $\sqrt n$-consistency.
--
--   **Formalization Note** Matrix norms are the spectral norm.
--
--   Differences from the source:
--   - generalization: the chain ending in (2.3), on the event $\sqrt n\|\hat\theta_{init}-\hat\theta\|<M$, for $C_n$, $g_n$, $h_n$ at $\hat\theta_{init}$, $\hat\theta$, multiplied by $\sqrt n$ and with $+\,o_P(1)$ → the inequality for fixed $C$, $g$, $h$ and arbitrary points $a$, $b$, with the common factor $\sqrt n$ and the error term removed; reason: multiplying by $\sqrt n$ and taking $a=\hat\theta_{init}$, $b=\hat\theta$ at each $\omega$ gives the paper's chain.
--   - encoding: the unspecified matrix norm of (2.3) → the spectral norm; reason: it is the operator norm for which the display's last step holds.
--   - encoding: $\operatorname{prox}$ as a function → any points of the set of minimizers; reason: existence is the caller's assumption.
--   - generalization: $H\succ0$ (assumption (i)) → $H$ any $d\times d$ matrix; reason: the display is pure algebra in $H$, and $H\succ0$ is a special case.
--   - generalization: $g_n$ continuously differentiable → $g$ differentiable at $a$ and $b$; reason: only $\nabla g(a)$, $\nabla g(b)$ appear, and a $C^1$ function is differentiable there.
-- source:
--   Bassett & Deride, One-Step Estimation with Scaled Proximal Methods, arXiv:2004.14521v3, proof of Theorem 2.1, (2.3), p.7

import Mathlib
import Definitions.Def_OneStepProx_IsProperConvex
import Definitions.Def_OneStepProx_scaledProx
import Definitions.Def_OneStepProx_eigenRatioSqrt

open scoped Matrix.Norms.L2Operator

namespace OneStepProx

/-- The deterministic core of (2.3) (Bassett & Deride, arXiv:2004.14521v3, proof of Theorem 2.1,
p.7): for `C ≻ 0`, a proper convex `h`, any matrix `H`, `g` differentiable at `a` and `b`, and
points `pa ∈ prox^C_h(a − C⁻¹∇g(a))`, `pb ∈ prox^C_h(b − C⁻¹∇g(b))`, with
`K = √(λmax(C)/λmin(C))`,
`‖pa − pb‖ ≤ K‖I − C⁻¹H‖ ‖a − b‖ + K‖C⁻¹‖ ‖∇g(a) − ∇g(b) − H(a − b)‖`.

**Formalization Note.** Matrix norms are the spectral norm (`Matrix.Norms.L2Operator`). The paper
applies this with `a = θ̂init`, `b = θ̂`, `C = Cₙ`, `g = gₙ`, multiplied by `√n`. -/
theorem oneStep_bound {d : ℕ} {C H : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef)
    {g : EuclideanSpace ℝ (Fin d) → ℝ} {D : Set (EuclideanSpace ℝ (Fin d))}
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hh : IsProperConvex D h)
    {a b pa pb : EuclideanSpace ℝ (Fin d)}
    (hga : DifferentiableAt ℝ g a) (hgb : DifferentiableAt ℝ g b)
    (hpa : pa ∈ scaledProx C D h (a - Matrix.toEuclideanLin C⁻¹ (gradient g a)))
    (hpb : pb ∈ scaledProx C D h (b - Matrix.toEuclideanLin C⁻¹ (gradient g b))) :
    ‖pa - pb‖ ≤ eigenRatioSqrt C * ‖1 - C⁻¹ * H‖ * ‖a - b‖
      + eigenRatioSqrt C * ‖C⁻¹‖ *
        ‖gradient g a - gradient g b - Matrix.toEuclideanLin H (a - b)‖ := by sorry

end OneStepProx
