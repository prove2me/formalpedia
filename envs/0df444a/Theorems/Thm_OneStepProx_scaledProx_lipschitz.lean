-- Prove2me | Theorems.Thm_OneStepProx_scaledProx_lipschitz
-- name    : OneStepProx.scaledProx_lipschitz
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:16.379392+00:00
-- url     : https://prove2.me/theorems/8e6a165e-1cf9-4169-95fb-1f5916e50f6a
-- title:
--   Proof of Theorem 2.1, p.7 — $\operatorname{prox}^C_h$ is $\sqrt{\lambda_{\max}(C)/\lambda_{\min}(C)}$-Lipschitz
-- statement:
--   Let $C\succ0$ be a $d\times d$ matrix with maximum and minimum eigenvalues $\lambda_{\max}(C)$, $\lambda_{\min}(C)$, and let $h:\mathbb R^d\to\mathbb R\cup\{\infty\}$ be proper and convex. For all $\theta_1,\theta_2$ and all $p_1\in\operatorname{prox}^C_h(\theta_1)$, $p_2\in\operatorname{prox}^C_h(\theta_2)$, in the Euclidean norm,
--
--   $$
--   \|p_1-p_2\|\le\sqrt{\frac{\lambda_{\max}(C)}{\lambda_{\min}(C)}}\;\|\theta_1-\theta_2\| .
--   $$
--
--   This transfers firm nonexpansiveness from the $C$-norm to the fixed Euclidean norm, at the cost of a constant that the proof of Theorem 2.1 controls in probability.
--
--   Differences from the source:
--   - generalization: the random $C_n$, $h_n$ for each $\omega$ → a fixed $C\succ0$ and a fixed proper convex $h$; reason: the paper applies a deterministic fact pointwise, and the Lean statement specializes to it at each $\omega$ of the almost sure event.
--   - encoding: $\operatorname{prox}$ as a function of $\theta$ → any points of the set of minimizers; reason: existence is the caller's assumption.
-- source:
--   Bassett & Deride, One-Step Estimation with Scaled Proximal Methods, arXiv:2004.14521v3, proof of Theorem 2.1, p.7, display after "Denote by λmax(Cn) and λmin(Cn)"

import Mathlib
import Definitions.Def_OneStepProx_IsProperConvex
import Definitions.Def_OneStepProx_scaledProx
import Definitions.Def_OneStepProx_eigenRatioSqrt

namespace OneStepProx

/-- Bassett & Deride, arXiv:2004.14521v3, proof of Theorem 2.1, p.7: for `C ≻ 0`, a proper convex
`h`, and points `p₁ ∈ prox^C_h(θ₁)`, `p₂ ∈ prox^C_h(θ₂)`,
`‖p₁ − p₂‖ ≤ √(λmax(C)/λmin(C)) ‖θ₁ − θ₂‖` in the Euclidean norm. -/
theorem scaledProx_lipschitz {d : ℕ} {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef)
    {D : Set (EuclideanSpace ℝ (Fin d))} {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hh : IsProperConvex D h) {θ₁ θ₂ p₁ p₂ : EuclideanSpace ℝ (Fin d)}
    (hp₁ : p₁ ∈ scaledProx C D h θ₁) (hp₂ : p₂ ∈ scaledProx C D h θ₂) :
    ‖p₁ - p₂‖ ≤ eigenRatioSqrt C * ‖θ₁ - θ₂‖ := by sorry

end OneStepProx
