-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_capReference_sum_le_one
-- name    : OAI.ProjectionMoments.capReference_sum_le_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:21:44.423788+00:00
-- url     : https://prove2.me/theorems/22f277f1-8132-4471-9237-084d62b98604
-- title:
--   Cap references of a partition of unity sum to at most one
-- statement:
--   Let $E$ be a finite-dimensional real inner product space, $k$ a natural number, and $(K_j)_{j\in J}$ a finite family of measurable kernels $K_j(X,z)\ge0$, with $X\in E^k$ and $z\in\mathbb R^k$, such that $\sum_jK_j\le1$ pointwise. For every $c\in E$ and $r\in\mathbb R$,
--   $$
--   \sum_{j\in J}\mathrm{ref}_{K_j}(c,r)\le1,
--   $$
--   where $\mathrm{ref}_K(c,r)=\int\!\!\int K\bigl(X,P_Xc+r\,R_Xz\bigr)\,d\beta_k(z)\,d\gamma^{\otimes k}(X)$ is the cap reference, with $\beta_k$ the uniform law on the unit ball of $\mathbb R^k$ and $\gamma$ the standard Gaussian.
--
--   So the reference budgets of a fractional partition add up to at most one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/CapDomination.lean#L72-L89

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
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity
import Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_RieszPotential
import Definitions.Def_OAI_Probability_ProjectionMoments_Polar
import Definitions.Def_OAI_Probability_ProjectionMoments_BallMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_CapTests
import Definitions.Def_OAI_Probability_ProjectionMoments_CapDuality
import Definitions.Def_OAI_Probability_ProjectionMoments_WeightedCover

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology

theorem OAI.ProjectionMoments.capReference_sum_le_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {k : ℕ} {J : Type*} [Fintype J]
    (K : J → (Fin k → E) × Label k → ℝ≥0∞) (hK : ∀ j, Measurable (K j))
    (hKsum : ∀ z, ∑ j, K j z ≤ 1) (c : E) (r : ℝ) : ∑ j, capReference (K j) c r ≤ 1 := by sorry
