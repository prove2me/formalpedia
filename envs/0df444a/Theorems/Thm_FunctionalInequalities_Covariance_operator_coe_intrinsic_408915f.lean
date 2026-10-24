-- Prove2me | Theorems.Thm_FunctionalInequalities_Covariance_operator_coe_intrinsic_408915f
-- name    : FunctionalInequalities.Covariance.operator_coe_intrinsic_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:13.823448+00:00
-- url     : https://prove2.me/theorems/c78d00bd-afa7-444c-9bf2-3200561ed3ce
-- title:
--   Ambient Covariance Operator on Intrinsic Directions
-- statement:
--   This states that the ambient covariance operator restricts to the intrinsic covariance operator on the affine-support direction space.
--
--   Let $E$ be a complete, finite-dimensional, second-countable real inner-product space with its Borel measurable structure. Let $\mu$ be a probability measure with finite second moment, let
--
--   $$
--   V=\operatorname{direction}(\operatorname{affineSupport}(\mu)),
--   $$
--
--   and let $v\in V$. Then, after coercing the intrinsic vector and intrinsic covariance output into $E$,
--
--   $$
--   \operatorname{Cov}(\mu)(v)
--   =
--   \operatorname{Cov}(\operatorname{intrinsicMeasure}(\mu))(v).
--   $$
--
--   This is the operator-level form of the ambient–intrinsic covariance correspondence and supports norm and positivity comparisons.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Covariance/Intrinsic.lean#L126-L152 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Covariance.Intrinsic`, declaration `FunctionalInequalities.Covariance.operator_coe_intrinsic`; the repository is private at upload time).

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

theorem FunctionalInequalities.Covariance.operator_coe_intrinsic_408915f (μ : ProbabilityMeasure E) (hμ : MemLp id 2 (μ : Measure E))
    (v : (affineSupport μ).direction) :
    operator (μ : Measure E) v =
      (operator (intrinsicMeasure μ : Measure (affineSupport μ).direction) v : E) := by sorry
