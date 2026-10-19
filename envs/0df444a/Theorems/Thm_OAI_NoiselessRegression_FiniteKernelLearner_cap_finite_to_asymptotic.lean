-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_FiniteKernelLearner_cap_finite_to_asymptotic
-- name    : OAI.NoiselessRegression.FiniteKernelLearner.cap_finite_to_asymptotic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:55:37.358062+00:00
-- url     : https://prove2.me/theorems/ffbab09d-3c38-4a93-9aee-133ef4bd139e
-- title:
--   Absorbing subquadratic memory into the exponential cap bound
-- statement:
--   Let $C\in\mathbb R$, $d\ge32$, and $M\le d^2$. Write $k=\lfloor d/16\rfloor$. Then for all $\varepsilon\ge0$, $\alpha\in\mathbb R$ and $n\in\mathbb N$,
--   $$
--   e^{Cd}\Bigl(\frac\varepsilon2\Bigr)^\alpha\Bigl(e^{Cd}\,2^{M/k}\Bigr)^n\le e^{(C+32)d(1+n)}\Bigl(\frac\varepsilon2\Bigr)^\alpha .
--   $$
--
--   This converts the finite fixed-stop bound into a form where memory enters only through the constant.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Asymptotics.lean#L164-L179

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
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u

theorem OAI.NoiselessRegression.FiniteKernelLearner.cap_finite_to_asymptotic (C : ℝ) {d M : ℕ} (hd : 32 ≤ d)
    (hM : (M:ℝ) ≤ (d:ℝ)^2) (ε α : ℝ) (n : ℕ) (hε : 0 ≤ ε) :
    Real.exp (C*d)*(ε/2)^α*(Real.exp (C*d)*(2:ℝ)^((M:ℝ)/(d/16:ℕ)))^n ≤
      Real.exp ((C+32)*d*(1+n))*(ε/2)^α := by sorry
