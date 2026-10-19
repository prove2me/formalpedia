-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_subquadratic_memory
-- name    : OAI.NoiselessRegression.subquadratic_memory
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T17:39:49.571035+00:00
-- url     : https://prove2.me/theorems/4ac9dd02-2dc4-43b5-8325-07289c5c299e
-- title:
--   Subquadratic memory forces a linear-times-logarithmic number of samples
-- statement:
--   There is $c>0$ such that for every memory budget $M(d)=o(d^2)$, eventually in $d$, every admissible learner with $M(d)$ bits estimating $s\in S^{d-1}$ to angular accuracy $\varepsilon\le\frac1{10}$ with success probability at least $\frac23$, either on average over the sphere or pointwise for every $s$, needs
--   $$
--   T\ge c\,d\log(1/\varepsilon)\ \text{samples}.
--   $$
--
--   In particular the bound applies to every memory budget of order $o(d^2)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Main.lean#L74-L89

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

theorem OAI.NoiselessRegression.subquadratic_memory : SubquadraticMemory.{u} := by sorry
