-- Prove2me | Theorems.Thm_GPhNGIDiffusion_OccupationCLT_proposition_3_1
-- name    : GPhNGIDiffusion.OccupationCLT.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:12.490813+00:00
-- url     : https://prove2.me/theorems/ef3d1f56-da58-40b3-ae23-e13ad61b7ff3
-- title:
--   Proposition 3.1, p. 12 — |f(x)|, |∇f(x)| ≤ C∥h∥_∞(1 + |x|²) for the Stein solution
-- statement:
--   Let $h:\mathbb R^d\to\mathbb R$ be bounded and measurable and let $f$ be the solution (3.2) of the Stein equation (3.1). Then $f$ is differentiable, and there is a constant $C>0$, independent of $h$ and $x$, such that for all $x\in\mathbb R^d$
--   $$
--   |f(x)|\le C\|h\|_\infty(1+|x|^2),\qquad |\nabla f(x)|\le C\|h\|_\infty(1+|x|^2).
--   $$
--
--   This regularity of the Stein solution is what makes Itô's formula applicable to $f(X_t)$ and gives the finiteness of the CLT variance $\mu(|\sigma'\nabla f|^2)$.
--
--   **Formalization Note** Differentiability of $f$ is part of the statement: the paper's $\nabla f$ is the gradient vector, and in Lean the gradient of a non-differentiable function is $0$. The constant is uniform in $h$, as in the proof (pp. 29–31) and as Theorem 1.3 uses it. The proof of Theorem 1.3 and §3.2 cite this result as "Lemma 3.1".
-- source:
--   Jin, Pang, Xu & Xu, An Approximation to the Invariant Measure of the Limiting Diffusion of G/Ph/n+GI Queues in the Halfin-Whitt Regime and Related Asymptotics, arXiv:2209.07361v1, p. 12, Proposition 3.1 (proof pp. 29–31)

import Mathlib
import Definitions.Def_GPhNGIDiffusion_OccupationCLT_Occupation
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GPhNGIDiffusion.OccupationCLT

/-- Proposition 3.1, p. 12. The solution `f` (3.2) of the Stein equation (3.1) for bounded
measurable `h` is differentiable, and `|f(x)| ≤ C∥h∥_∞(1 + |x|²)`,
`|∇f(x)| ≤ C∥h∥_∞(1 + |x|²)` with `C` independent of `h` and `x`. -/
theorem proposition_3_1 {d : ℕ} (M : Model d) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (B : ℝ≥0 → Ω → E d) (X : E d → ℝ≥0 → Ω → E d) (hX : IsDiffusion M P B X)
    (μ : Measure (E d)) [IsProbabilityMeasure μ] (hμ : IsInvariant P X μ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : E d → ℝ, Measurable h → (∃ K : ℝ, ∀ y, |h y| ≤ K) →
      Differentiable ℝ (steinSol P X μ h) ∧
      ∀ x : E d,
        |steinSol P X μ h x| ≤ C * supNorm h * (1 + ‖x‖ ^ 2) ∧
        ‖gradient (steinSol P X μ h) x‖ ≤ C * supNorm h * (1 + ‖x‖ ^ 2) := by sorry

end GPhNGIDiffusion.OccupationCLT
