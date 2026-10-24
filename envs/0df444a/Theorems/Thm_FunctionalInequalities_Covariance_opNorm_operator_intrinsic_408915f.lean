-- Prove2me | Theorems.Thm_FunctionalInequalities_Covariance_opNorm_operator_intrinsic_408915f
-- name    : FunctionalInequalities.Covariance.opNorm_operator_intrinsic_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:13.778759+00:00
-- url     : https://prove2.me/theorems/302f1956-fbd2-4ecb-b6ef-b4ebb0aa9123
-- title:
--   Equality of Ambient and Intrinsic Covariance Norms
-- statement:
--   This proves equality of the operator norms of the ambient and intrinsic covariance operators.
--
--   Let $E$ be a complete, finite-dimensional, second-countable real inner-product space with its Borel measurable structure, and let $\mu$ be a probability measure on $E$ with finite second moment. If $V$ is the direction of the affine support of $\mu$, then
--
--   $$
--   \left\|\operatorname{Cov}(\operatorname{intrinsicMeasure}(\mu))\right\|
--   =
--   \left\|\operatorname{Cov}(\mu)\right\|.
--   $$
--
--   The intrinsic operator acts on $V$, while the ambient operator acts on $E$.
--
--   This equality allows operator-norm estimates to be transferred between intrinsic and ambient formulations.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Covariance/Intrinsic.lean#L154-L179 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Covariance.Intrinsic`, declaration `FunctionalInequalities.Covariance.opNorm_operator_intrinsic`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Probability.Moments.CovarianceBilin

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace E] [BorelSpace E]
variable [SecondCountableTopology E] [FiniteDimensional ℝ E]
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Covariance
end FunctionalInequalities.Covariance
open FunctionalInequalities FunctionalInequalities.Covariance
open Probability

theorem FunctionalInequalities.Covariance.opNorm_operator_intrinsic_408915f (μ : ProbabilityMeasure E) (hμ : MemLp id 2 (μ : Measure E)) :
    ‖operator (intrinsicMeasure μ : Measure (affineSupport μ).direction)‖ =
      ‖operator (μ : Measure E)‖ := by sorry
