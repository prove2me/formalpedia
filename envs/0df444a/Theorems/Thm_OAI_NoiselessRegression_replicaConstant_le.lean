-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_replicaConstant_le
-- name    : OAI.NoiselessRegression.replicaConstant_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:35:35.833035+00:00
-- url     : https://prove2.me/theorems/5e275519-08aa-4550-9824-ac0b67ac7482
-- title:
--   The replica constant is exponential in the dimension
-- statement:
--   Let $\nu$ have total mass at most $1$ on a space of dimension $n\ge1$, and let $a,m\le n$ be natural numbers. Then the replica constant satisfies
--   $$
--   \nu(E)+3^n4^a\,2^{m+1}\le128^n .
--   $$
--
--   So the replica moment bounds lose at most a factor exponential in the dimension.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Blocks.lean#L89-L112

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

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise
universe u
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
theorem OAI.NoiselessRegression.replicaConstant_le {ν : Measure E} (hν : ν univ ≤ 1) {a m : ℕ}
    (hd : 1 ≤ Module.finrank ℝ E) (ha : a ≤ Module.finrank ℝ E) (hm : m ≤ Module.finrank ℝ E) :
    replicaConstant ν (a : ℝ) m ≤ (128 : ℝ≥0∞) ^ Module.finrank ℝ E := by sorry
