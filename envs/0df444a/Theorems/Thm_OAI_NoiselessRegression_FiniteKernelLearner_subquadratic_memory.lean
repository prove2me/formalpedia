-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_FiniteKernelLearner_subquadratic_memory
-- name    : OAI.NoiselessRegression.FiniteKernelLearner.subquadratic_memory
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:53:38.769376+00:00
-- url     : https://prove2.me/theorems/871a514f-895d-4ffa-a374-74d21dfd1c8f
-- title:
--   Seeded kernel learners with subquadratic memory need many samples
-- statement:
--   A finite kernel learner with $M$ bits of memory and horizon $T$ on $\mathbb R^d$ consists of an initial law on $\{\text{stop},\text{continue}\}\times\mathrm{State}$, transition kernels $K_t(j,\mathrm{obs})$ on the same set, and output laws on the unit sphere, where $|\mathrm{State}|=2^M$. It reads noiseless observations $(x_i,\langle s,x_i\rangle)$ with Gaussian $x_i$. It has completed rules if each transition probability $\mathrm{obs}\mapsto K_t(j,\mathrm{obs})\{a\}$ is measurable with respect to the completion of the observation reference law (Gaussian times Lebesgue). Its uniform success at accuracy $\varepsilon$ is the probability that the output has angular error at most $\varepsilon$, for uniform $s$ and Gaussian samples; the fixed-time success additionally requires the stop to happen at time $t$. For a seed space $(\Xi,\rho)$ and learners $K_\xi$, the seeded success is $\int\mathrm{succ}(K_\xi,\varepsilon)\,d\rho(\xi)$. There is $c>0$ such that for every memory function $M(d)=o(d^2)$ there is $d_0$ with the following property. Let $d\ge d_0$, $0<\varepsilon\le1/10$, and let $(K_\xi)$ be seeded finite kernel learners with memory $M(d)$ and horizon $T$, with completed rules for almost every seed. If their seeded success is at least $2/3$, then
--   $$
--   T\ge c\,d\log\frac1\varepsilon .
--   $$
--
--   So subquadratic memory forces a sample count of order $d\log(1/\varepsilon)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Seeded.lean#L220-L231

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
import Definitions.Def_OAI_Probability_ProjectionMoments_Stopping
import Definitions.Def_OAI_Probability_ProjectionMoments_BorelRules
import Definitions.Def_OAI_Probability_ProjectionMoments_Kernels
import Definitions.Def_OAI_Probability_ProjectionMoments_Realization
import Definitions.Def_OAI_Probability_ProjectionMoments_StoppingKernel
import Definitions.Def_OAI_Probability_ProjectionMoments_Seeded

open OAI OAI.NoiselessRegression OAI.NoiselessRegression.FiniteKernelLearner
open MeasureTheory ProbabilityTheory Set Filter unitInterval
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
variable {d M T : ℕ}

theorem OAI.NoiselessRegression.FiniteKernelLearner.subquadratic_memory : SubquadraticMemory.{u} := by sorry
