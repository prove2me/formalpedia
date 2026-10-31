-- Prove2me | Theorems.Thm_OneStepProx_scaledProx_firmlyNonexpansive
-- name    : OneStepProx.scaledProx_firmlyNonexpansive
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:10:32.504221+00:00
-- url     : https://prove2.me/theorems/b1b30f95-e4c8-430d-8e2e-1795146becb3
-- title:
--   Proof of Theorem 2.1, pp.6–7 — $\operatorname{prox}^C_h$ is firmly nonexpansive in the $C$-norm
-- statement:
--   Let $C\succ0$ be a $d\times d$ matrix and $h:\mathbb R^d\to\mathbb R\cup\{\infty\}$ proper and convex. For all $\theta_1,\theta_2\in\mathbb R^d$ and all $p_1\in\operatorname{prox}^C_h(\theta_1)$, $p_2\in\operatorname{prox}^C_h(\theta_2)$,
--
--   $$
--   (p_1-p_2)^{T}C\bigl((\theta_1-p_1)-(\theta_2-p_2)\bigr)\ge0
--   \qquad\text{and}\qquad
--   \|p_1-p_2\|_C\le\|\theta_1-\theta_2\|_C .
--   $$
--
--   In particular the scaled proximal operator is single-valued where it is nonempty. This is the first step of the proof of Theorem 2.1.
--
--   **Formalization Note** The second inequality is stated on the squares $\|\cdot\|_C^2$.
--
--   Differences from the source:
--   - generalization: the random $C_n$, $h_n$ for each $\omega$ → a fixed $C\succ0$ and a fixed proper convex $h$; reason: the paper applies a deterministic fact pointwise, and the Lean statement specializes to it at each $\omega$ of the almost sure event.
--   - encoding: $\|\theta_1-\theta_2\|_{C}\ge\|p_1-p_2\|_{C}$ → the same inequality between the squares; reason: both sides are nonnegative for $C\succ0$.
--   - encoding: $\operatorname{prox}$ as a function of $\theta$ → any points of the set of minimizers; reason: the prox is set-valued until this result; existence is the caller's assumption.
-- source:
--   Bassett & Deride, One-Step Estimation with Scaled Proximal Methods, arXiv:2004.14521v3, proof of Theorem 2.1, pp.6–7, "Therefore prox is firmly nonexpansive in the Cn norm"

import Mathlib
import Definitions.Def_OneStepProx_scaledSqNorm
import Definitions.Def_OneStepProx_IsProperConvex
import Definitions.Def_OneStepProx_scaledProx

open scoped RealInnerProductSpace

namespace OneStepProx

/-- Bassett & Deride, arXiv:2004.14521v3, proof of Theorem 2.1, pp.6–7, "Therefore prox is firmly
nonexpansive in the Cn norm": for `C ≻ 0`, a proper convex `h`, and points `p₁ ∈ prox^C_h(θ₁)`,
`p₂ ∈ prox^C_h(θ₂)`, one has `(p₁ − p₂)ᵀ C ((θ₁ − p₁) − (θ₂ − p₂)) ≥ 0` and
`‖θ₁ − θ₂‖_C ≥ ‖p₁ − p₂‖_C`.

**Formalization Note.** `C ≻ 0` is `Matrix.PosDef`, which includes symmetry. The prox is a set, so
the statement is about any two of its points; the case `θ₁ = θ₂` gives single-valuedness. The
`C`-norm inequality is stated on the squares `‖·‖²_C`, which are nonnegative for `C ≻ 0`. -/
theorem scaledProx_firmlyNonexpansive {d : ℕ} {C : Matrix (Fin d) (Fin d) ℝ} (hC : C.PosDef)
    {D : Set (EuclideanSpace ℝ (Fin d))} {h : EuclideanSpace ℝ (Fin d) → ℝ}
    (hh : IsProperConvex D h) {θ₁ θ₂ p₁ p₂ : EuclideanSpace ℝ (Fin d)}
    (hp₁ : p₁ ∈ scaledProx C D h θ₁) (hp₂ : p₂ ∈ scaledProx C D h θ₂) :
    0 ≤ ⟪p₁ - p₂, Matrix.toEuclideanLin C ((θ₁ - p₁) - (θ₂ - p₂))⟫ ∧
      scaledSqNorm C (p₁ - p₂) ≤ scaledSqNorm C (θ₁ - θ₂) := by sorry

end OneStepProx
