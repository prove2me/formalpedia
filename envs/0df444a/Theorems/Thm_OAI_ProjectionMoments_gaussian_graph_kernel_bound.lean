-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_gaussian_graph_kernel_bound
-- name    : OAI.ProjectionMoments.gaussian_graph_kernel_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:40:29.056988+00:00
-- url     : https://prove2.me/theorems/0bb15b0b-141b-4e06-8d27-5402652801b6
-- title:
--   Gaussian averages of products of smoothing kernels
-- statement:
--   Let $v_1,\dots,v_n$ be linearly independent vectors with Gram–Schmidt vectors $g_i$, and let $\varphi\ge0$ be a measurable probability density on $\mathbb R^m$. For every $b\in\mathbb R^m$,
--   $$
--   \int\prod_{i=1}^n\varphi\bigl(b-(\langle v_i,A_j\rangle)_j\bigr)\,d\gamma^{\otimes m}(A)\le\Bigl(\prod_i\|g_i\|\Bigr)^{-m},
--   $$
--   where $A=(A_1,\dots,A_m)$ are independent standard Gaussian rows.
--
--   Nearly dependent replicas, with small Gram–Schmidt lengths, receive larger weight.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Graph.lean#L39-L67

import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.ProjectionMoments.gaussian_graph_kernel_bound {n : ℕ} (v : Fin n → E)
    (hv : LinearIndependent ℝ v) (m : ℕ)
    (φ : (Fin m → ℝ) → ℝ≥0∞) (hφ : Measurable φ)
    (hφ1 : ∫⁻ y, φ y = 1) (b : Fin m → ℝ) :
    ∫⁻ A : Fin m → E, ∏ i, φ (fun j => b j - ⟪v i, A j⟫)
      ∂Measure.pi (fun _ => stdGaussian E) ≤
      ENNReal.ofReal ((∏ i, ‖gramSchmidt ℝ v i‖)⁻¹ ^ m) := by sorry
