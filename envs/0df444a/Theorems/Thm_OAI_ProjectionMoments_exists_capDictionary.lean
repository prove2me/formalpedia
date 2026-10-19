-- Prove2me | Theorems.Thm_OAI_ProjectionMoments_exists_capDictionary
-- name    : OAI.ProjectionMoments.exists_capDictionary
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:12:16.022254+00:00
-- url     : https://prove2.me/theorems/44bfc346-62ec-489d-9988-1a02c715965c
-- title:
--   Existence of a multiscale dictionary of spherical caps
-- statement:
--   Let $c$ be a unit vector in a finite-dimensional real inner product space $E$, and let $r>0$ and $\alpha\ge1$. Then there exists a cap dictionary for $(c,r,\alpha)$. This is a countable family of unit centres $c_i$ and radii $0<\rho_i\le r$ with the following properties. It contains the parent cap $(c,r)$. For each $R$ only finitely many $i$ satisfy $(r/\rho_i)^\alpha\le R$. For every unit vector $s$ and every $0<t\le1/4$ there is an index $i$ with
--   $$
--   4rt\le\rho_i<8rt\qquad\text{and}\qquad\|s-c_i\|\le\rho_i/2 .
--   $$
--
--   These caps are used as test sets for the dual mass condition.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Caps.lean#L257-L332

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

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.ProjectionMoments.exists_capDictionary {c : E} (hc : ‖c‖ = 1) {r α : ℝ}
    (hr : 0 < r) (hα : 1 ≤ α) : Nonempty (CapDictionary c r α) := by sorry
