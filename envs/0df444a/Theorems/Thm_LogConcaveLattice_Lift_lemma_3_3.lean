-- Prove2me | Theorems.Thm_LogConcaveLattice_Lift_lemma_3_3
-- name    : LogConcaveLattice.Lift.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:01:30.401938+00:00
-- url     : https://prove2.me/theorems/936ddb9f-6728-4b52-9240-4ccc7823b273
-- title:
--   Lemma 3.3 — $\nabla^2(-\log f)(x)=4\pi^2A^{-1}\operatorname{Cov}(D_{x+\Lambda,A})A^{-1}$
-- statement:
--   Let $\Lambda\subseteq\mathbb R^n$ be a full-rank lattice, let $A\succ0$ be symmetric, and let
--   $$f(x)=\frac1{\det\Lambda}\cdot\frac{\rho_A(x)}{\rho_A(x+\Lambda)},\qquad \rho_A(x)=e^{-\pi\langle x,A^{-1}x\rangle}.$$
--   Then $f$ is smooth and
--   $$\nabla^2(-\log f)(x)=4\pi^2A^{-1}\operatorname{Cov}(D_{x+\Lambda,A})A^{-1}\qquad\text{for every }x\in\mathbb R^n,$$
--   where $D_{x+\Lambda,A}$ is the discrete Gaussian on $x+\Lambda$ with $\mathbb P(Y=y)=\rho_A(y)/\rho_A(x+\Lambda)$.
--
--   Together with Lemma 3.2 this reduces strong log-concavity of $f$ to a lower bound on $\operatorname{Cov}(D_{\Lambda,A})$.
--
--   Differences from the source:
--   - generalization: ∇²(−log f)(x) = 4π² A⁻¹ Cov(D_{x+Λ,A}) A⁻¹ → additionally f is C^∞; reason: smoothness of this explicitly constructed f is stated on p. 9; the added conjunct strengthens the standalone lemma while retaining its full Hessian identity, and supplies genuine differentiability for Lean's total fderiv
--   - encoding: equality of Hessian matrices → equality of bilinear forms D²(−log f)(x)(u, v) = 4π²⟨u, A⁻¹ Cov A⁻¹ v⟩ for all u, v; the weight ρ_A through the pseudoinverse; reason: a symmetric matrix is determined by its bilinear form; A⁺ = A⁻¹ for A ≻ 0
-- source:
--   Letwin, Reis, Rothvoss, Strongly Log-Concave Measures and Lattices, STOC 2027 submission #401 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/401.pdf, Lemma 3.3, p. 11 (density f p. 11 and p. 9; proof p. 12)

import Mathlib
import Definitions.Def_LogConcaveLattice_Lift_Lattice
import Definitions.Def_LogConcaveLattice_Lift_Gaussian

open scoped RealInnerProductSpace

namespace LogConcaveLattice.Lift

/-- **Lemma 3.3** (p. 11): for a full-rank lattice `Λ ⊆ ℝⁿ`, a symmetric `A ≻ 0` and the
density `f(x) = (1/det Λ) ρ_A(x) / ρ_A(x + Λ)`, the function `f` is smooth and
`∇²(−log f)(x) = 4π² A⁻¹ Cov(D_{x+Λ,A}) A⁻¹` for every `x ∈ ℝⁿ`, as bilinear forms:
`D²(−log f)(x)(u, v) = 4π² ⟨u, A⁻¹ Cov(D_{x+Λ,A}) A⁻¹ v⟩`. -/
theorem lemma_3_3 (n : ℕ) (Λ : Submodule ℤ (V n)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    ContDiff ℝ (⊤ : ℕ∞) (liftDensity A Λ) ∧
      ∀ x u v : V n,
        fderiv ℝ (fderiv ℝ (fun y => -Real.log (liftDensity A Λ y))) x u v =
          4 * Real.pi ^ 2 * ⟪u, mat (A⁻¹ * dgCov A Λ x * A⁻¹) v⟫ := by sorry

end LogConcaveLattice.Lift
