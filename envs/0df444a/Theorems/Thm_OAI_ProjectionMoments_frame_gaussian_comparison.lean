-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_frame_gaussian_comparison
-- name    : OAI.ProjectionMoments.frame_gaussian_comparison
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:54:35.055224+00:00
-- url     : https://prove2.me/theorems/0895c285-40e2-499e-9be1-f12d5188ed4c
-- title:
--   Frame moments are controlled by Gaussian moments
-- statement:
--   For a finite measure $\nu$ on a finite-dimensional inner product space $E$ (of dimension $n$) and rows $A=(A_1,\dots,A_m)$, $f_\nu(A,\cdot)$ is the coordinate density of the projection $x\mapsto(\langle x,A_i\rangle)_i$; the frame law of an orthonormal family $u$ is the image of Haar measure on rotations under $O\mapsto Ou$; the label moment is $\int f_\nu(A,y)^{n'+1}dy$ and the orbit moment averages it over the frame law. If $m\le n$, $u$ is an orthonormal $m$-frame and almost every frame projection of $\nu$ is absolutely continuous, then for every $n'$,
--   $$
--   \mathrm{orbitMoment}_{n'}(u)\le2^m\,(\sqrt{2n})^{m n'}\int\mathrm{labelMoment}_{n'}(A)\,d\gamma^{\otimes m}(A).
--   $$
--
--   Uniformly random orthonormal frames can thus be replaced by independent Gaussian rows.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Frames.lean#L332-L385

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

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.ProjectionMoments.frame_gaussian_comparison (ν : Measure E) [IsFiniteMeasure ν]
    {m n : ℕ} (hm : m ≤ Module.finrank ℝ E) (hd : 0 < Module.finrank ℝ E)
    (u : Fin m → E) (hu : Orthonormal ℝ u)
    (hac : ∀ᵐ A ∂frameLaw u, ν.map (coordinateMap A) ≪ (volume : Measure (Fin m → ℝ))) :
    orbitMoment ν m n u ≤
      (2 : ℝ≥0∞)^m * ENNReal.ofReal (Real.sqrt (2 * Module.finrank ℝ E))^(m*n) *
        ∫⁻ A, labelMoment ν m n A ∂Measure.pi (fun _ => stdGaussian E) := by sorry
