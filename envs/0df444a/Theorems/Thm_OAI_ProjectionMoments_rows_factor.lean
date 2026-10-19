-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_rows_factor
-- name    : OAI.ProjectionMoments.rows_factor
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:53:50.281199+00:00
-- url     : https://prove2.me/theorems/7c40fb7b-c1a0-41ae-ab30-d9d6e3750339
-- title:
--   Linearly independent rows factor through an orthonormal frame
-- statement:
--   Let $A_1,\dots,A_m$ be linearly independent vectors with Gram–Schmidt vectors $g_i$. Then there are an orthonormal family $u_1,\dots,u_m$ and a linear isomorphism $T$ of $\mathbb R^m$ such that the coordinate maps satisfy
--   $$
--   (\langle x,A_i\rangle)_i=T\bigl((\langle x,u_i\rangle)_i\bigr),
--   $$
--   and $T$ scales Lebesgue measure by $\bigl(\prod_i\|g_i\|\bigr)^{-1}$, i.e. $T_*\mathrm{vol}=(\prod_i\|g_i\|)^{-1}\mathrm{vol}$.
--
--   Projections onto general rows thus reduce to projections onto orthonormal frames.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Frames.lean#L131-L166

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
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem OAI.ProjectionMoments.rows_factor {m : ℕ} (A : Fin m → E) (hA : LinearIndependent ℝ A) :
    ∃ u : Fin m → E, Orthonormal ℝ u ∧
      ∃ T : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ),
        (∀ x, coordinateMap A x = T (coordinateMap u x)) ∧
        (volume : Measure (Fin m → ℝ)).map T =
          (ENNReal.ofReal (rowJacobian A))⁻¹ • volume := by sorry
