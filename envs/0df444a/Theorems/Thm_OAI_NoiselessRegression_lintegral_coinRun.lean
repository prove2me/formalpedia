-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_lintegral_coinRun
-- name    : OAI.NoiselessRegression.lintegral_coinRun
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:32:06.547681+00:00
-- url     : https://prove2.me/theorems/a4bad2d7-ccb0-4476-88ca-a5693deab593
-- title:
--   Coin-driven runs realize the kernel run
-- statement:
--   Let $J$ be finite, and let the measurable maps $F_t(j,o,\cdot):[0,1]\to J$ push Lebesgue measure to the kernels $P_t(j,o)$. Let $R_n(j,o,u)$ be the coin run ($R_0=j$, $R_{t+1}=F_{t+1}(R_t,o_{t+1},u_{t+1})$) and $\mathrm{run}_n(j,o)$ the kernel run ($\delta_j$, then successively bound with $P_{t+1}(\cdot,o_{t+1})$). Then for every $f:J\to[0,\infty]$,
--   $$
--   \int_{[0,1]^n}f\bigl(R_n(j,o,u)\bigr)\,du=\int f\,d\,\mathrm{run}_n(j,o).
--   $$
--
--   Independent uniform coins thus realize the Markov chain given by the kernels.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ProjectionMoments/Kernels.lean#L86-L105

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

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped ENNReal NNReal RealInnerProductSpace
variable {J O : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace O]

theorem OAI.NoiselessRegression.lintegral_coinRun {F : ℕ → J → O → I → J} {P : ℕ → J → O → Measure J}
    (hF : ∀ t j obs, Measurable (F t j obs))
    (hP : ∀ t j obs, volume.map (F t j obs) = P t j obs)
    (n : ℕ) (j : J) (obs : Fin n → O) (f : J → ℝ≥0∞) :
    (∫⁻ u, f (coinRun F n j obs u) ∂Measure.pi (fun _ => (volume : Measure I))) =
      ∫⁻ a, f a ∂kernelRun P n j obs := by sorry
