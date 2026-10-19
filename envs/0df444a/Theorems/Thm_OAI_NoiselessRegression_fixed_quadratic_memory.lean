-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_fixed_quadratic_memory
-- name    : OAI.NoiselessRegression.fixed_quadratic_memory
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:36:44.499409+00:00
-- url     : https://prove2.me/theorems/68c12f2a-3df0-43b1-bb4d-8da59bcb3d7f
-- title:
--   Quadratic memory forces a linear-times-logarithmic number of samples
-- statement:
--   For every $A_0>0$ there are $c>0$ and $d_0$ such that, for all $d\ge d_0$, memory $M\le A_0d^2$ bits, $T$ samples and accuracy $0<\varepsilon\le\frac1{10}$, every admissible learner of an unknown unit vector $s\in S^{d-1}$ from noiseless Gaussian observations $(x_i,\langle x_i,s\rangle)$ whose average success probability over the uniform sphere is at least $\frac23$ satisfies
--   $$
--   T\ge c\,d\log(1/\varepsilon).
--   $$
--
--   This is the quadratic-memory lower bound for noiseless Gaussian linear regression.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Main.lean#L20-L38

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

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise
universe u

theorem OAI.NoiselessRegression.fixed_quadratic_memory : FixedQuadraticMemory.{u} := by sorry
