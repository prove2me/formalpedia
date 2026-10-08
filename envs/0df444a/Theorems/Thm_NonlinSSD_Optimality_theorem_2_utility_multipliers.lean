-- Prove2me | Theorems.Thm_NonlinSSD_Optimality_theorem_2_utility_multipliers
-- name    : NonlinSSD.Optimality.theorem_2_utility_multipliers
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:00:49.955313+00:00
-- url     : https://prove2.me/theorems/b9130739-d4e6-42c2-a81f-6d75ed950667
-- title:
--   Theorem 2 — utility and L∞ multiplier optimality conditions
-- statement:
--   Assume the uniform dominance condition of Definition 1 for the split program (11)–(14). If $(\hat z,\hat X)$ is an optimal solution, then there are utilities $\hat u_i\in\mathcal U_1([a_i,b_i])$ and essentially bounded, almost surely nonnegative multipliers $\hat\theta_i$ satisfying
--   $$L(\hat z,\hat X,\hat u,\hat\theta)=\max_{z\in Z,\,X\in\mathcal L_1^m}L(z,X,\hat u,\hat\theta),\qquad \mathbb E[\hat u_i(\hat X_i)]=\mathbb E[\hat u_i(Y_i)],\qquad \hat\theta_i(\hat X_i-G_i(\hat z))=0\ \text{a.s.}$$
--   Conversely, if a pair $(\hat z,\hat X)$ attains that Lagrangian maximum for admissible $\hat u,\hat\theta$, satisfies interval dominance and $\hat X_i\le G_i(\hat z)$ almost surely, and obeys both complementarity equalities, then it is an optimal solution of (11)–(14).
--
--   The theorem characterizes primal optima using concave utility multipliers for the dominance constraints and $L^\infty$ multipliers for the split outcome inequalities.
--
--   **Formalization Note** The printed definition of $\mathcal U_1$ says $c>0$ below $a$; the formalization corrects this to $c\ge0$, because the zero utility is necessary and the strict form makes the theorem false. The Lagrangian maximum is attained over integrable $X$, equality (20) is almost sure, and the theorem's opening uniform dominance hypothesis is retained for the converse although its proof does not use it.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), p. 7, Theorem 2; proof pp. 7–11

import Mathlib
import Definitions.Def_NonlinSSD_Optimality_Basic

namespace NonlinSSD.Optimality

open MeasureTheory

/-- Theorem 2, p. 7: necessity and sufficiency of the utility and L∞ multiplier
conditions under uniform dominance. The converse does not use this regularity
condition, but it is retained under the theorem's opening hypothesis. -/
theorem theorem_2_utility_multipliers
    {Ω 𝒵 : Type*} [MeasurableSpace Ω]
    [AddCommGroup 𝒵] [Module ℝ 𝒵] [TopologicalSpace 𝒵]
    [IsTopologicalAddGroup 𝒵] [ContinuousSMul ℝ 𝒵]
    [LocallyConvexSpace ℝ 𝒵] [T2Space 𝒵]
    [TopologicalSpace.SeparableSpace 𝒵]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ}
    (pr : Problem Ω 𝒵 P m) (hdom : pr.UniformDominance) :
    (∀ z : 𝒵, ∀ X : Fin m → Ω → ℝ,
      pr.IsOptimal z X →
      ∃ u : Fin m → ℝ → ℝ, ∃ θ : Fin m → Ω → ℝ,
        pr.UtilityAdmissible u ∧ pr.MultiplierAdmissible θ ∧
        pr.MaximizesL z X u θ ∧ pr.Complementary z X u θ) ∧
    (∀ z : 𝒵, ∀ X : Fin m → Ω → ℝ,
      ∀ u : Fin m → ℝ → ℝ, ∀ θ : Fin m → Ω → ℝ,
      pr.UtilityAdmissible u → pr.MultiplierAdmissible θ →
      pr.MaximizesL z X u θ → pr.Dominates X →
      (∀ i, X i ≤ᵐ[P] pr.G i z) →
      pr.Complementary z X u θ → pr.IsOptimal z X) := by sorry

end NonlinSSD.Optimality
