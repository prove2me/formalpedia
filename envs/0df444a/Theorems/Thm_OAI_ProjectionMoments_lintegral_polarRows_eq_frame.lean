-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_lintegral_polarRows_eq_frame
-- name    : OAI.ProjectionMoments.lintegral_polarRows_eq_frame
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:00:46.882481+00:00
-- url     : https://prove2.me/theorems/65640966-50cc-49d9-b4bc-ba4da5388201
-- title:
--   Polar-normalized Gaussian rows have the frame law
-- statement:
--   Let $k\le\dim E$ and let $u$ be an orthonormal $k$-frame. For independent standard Gaussian rows $X=(X_1,\dots,X_k)$, the polar normalization $(X^\top X)^{-1/2}X$ (with fallback $u$ on the null set of dependent rows) is distributed according to the frame law of $u$:
--   $$
--   \int f\bigl(\mathrm{polar}_u(X)\bigr)\,d\gamma^{\otimes k}(X)=\int f(A)\,d\mathrm{frame}_u(A)
--   $$
--   for every measurable $f\ge0$.
--
--   So polar-normalized Gaussian rows can replace uniformly random frames in all integrals of this kind.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Polar.lean#L148-L180

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

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace Matrix
open scoped ENNReal NNReal RealInnerProductSpace Topology MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.ProjectionMoments.lintegral_polarRows_eq_frame {k : ℕ} (hk : k ≤ Module.finrank ℝ E)
    {u : Fin k → E} (hu : Orthonormal ℝ u) (f : (Fin k → E) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ X, f (polarRows u X) ∂Measure.pi (fun _ => stdGaussian E)) = ∫⁻ A, f A ∂frameLaw u := by sorry
