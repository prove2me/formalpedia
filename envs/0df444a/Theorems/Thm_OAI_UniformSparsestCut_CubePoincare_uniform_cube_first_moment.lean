-- Prove2me | Theorems.Thm_OAI_UniformSparsestCut_CubePoincare_uniform_cube_first_moment
-- name    : OAI.UniformSparsestCut.CubePoincare.uniform_cube_first_moment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:46:19.562995+00:00
-- url     : https://prove2.me/theorems/dc48791a-5c97-41dd-a18f-06499967b692
-- title:
--   L¹ Poincaré inequality with constant π/2 on the cube [−1, 1]ᵐ with uniform measure: E|h(U) − h(V)| ≤ (π/2)·E‖Dh(U)‖
-- statement:
--   Let $m \in \mathbb N$ and let $\lambda_m$ be the uniform probability measure on the open cube $(-1, 1)^m$, viewed in the Euclidean space $\mathbb R^m$ (`EuclideanSpace ℝ (Fin m)`): in Lean, the product over `Fin m` of the measures $\tfrac12\,\mathrm{Leb}|_{(-1,1)}$ (`(2 : ℝ≥0∞)⁻¹ • volume.restrict (Ioo (-1 : ℝ) 1)`), pushed forward by `WithLp.toLp 2`. Let $h : \mathbb R^m \to \mathbb R$ be continuously differentiable (`ContDiff ℝ 1 h`), with Fréchet derivative $Dh(x)$ (`fderiv ℝ h x`, operator norm). Then
--   $$\int |h(x) - h(y)|\,d(\lambda_m \otimes \lambda_m)(x, y) \;\le\; \frac{\pi}{2} \int \|Dh(x)\|\,d\lambda_m(x).$$
--
--   Lean: `OAI.UniformSparsestCut.CubePoincare.uniform_cube_first_moment`. It uses only Mathlib. OpenAI's theorem `cube_first_moment` states the same with its definition `cube` of the uniform measure; this statement unfolds it, and OpenAI's theorem is proved from it.
-- source:
--   Classical in the Gaussian case (the rotation argument of B. Maurey and G. Pisier; G. Pisier, Probabilistic methods in the geometry of Banach spaces, in: Probability and Analysis (Varenna, 1985), Lecture Notes in Mathematics 1206, Springer, 1986, pp. 167–241), transferred to the cube by the coordinatewise map x ↦ 2Φ(x) − 1. Proof: OpenAI, Near-square-root logarithmic integrality gaps for uniform sparsest cut, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 117, commit adc7f12, Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SparsestCut/CubePoincare.lean (OpenAI's theorem OAI.UniformSparsestCut.CubePoincare.cube_first_moment, restated with its definitions unfolded)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.CubePoincare
open MeasureTheory ProbabilityTheory Set
open scoped Topology ContDiff ENNReal BigOperators
variable {m : ℕ}

theorem uniform_cube_first_moment (h : EuclideanSpace ℝ (Fin m) → ℝ) (hh : ContDiff ℝ 1 h) :
    (∫ z : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m), |h z.1 - h z.2| ∂
      (((Measure.pi (fun _ : Fin m => (2 : ℝ≥0∞)⁻¹ • volume.restrict (Ioo (-1 : ℝ) 1))).map
          (WithLp.toLp 2)).prod
        ((Measure.pi (fun _ : Fin m => (2 : ℝ≥0∞)⁻¹ • volume.restrict (Ioo (-1 : ℝ) 1))).map
          (WithLp.toLp 2)))) ≤
      (Real.pi / 2) * ∫ x, ‖fderiv ℝ h x‖ ∂((Measure.pi
        (fun _ : Fin m => (2 : ℝ≥0∞)⁻¹ • volume.restrict (Ioo (-1 : ℝ) 1))).map (WithLp.toLp 2)) := by
  sorry

end UniformSparsestCut.CubePoincare

end

end OAI
end
