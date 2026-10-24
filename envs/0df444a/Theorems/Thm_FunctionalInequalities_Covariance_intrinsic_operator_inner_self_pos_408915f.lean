-- Prove2me | Theorems.Thm_FunctionalInequalities_Covariance_intrinsic_operator_inner_self_pos_408915f
-- name    : FunctionalInequalities.Covariance.intrinsic_operator_inner_self_pos_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:12.478238+00:00
-- url     : https://prove2.me/theorems/6282e792-153b-49c5-8e67-77eb5470e04a
-- title:
--   Positive Definiteness of Intrinsic Covariance
-- statement:
--   This proves positive definiteness of the intrinsic covariance operator on the affine-support direction space.
--
--   Let $E$ be a finite-dimensional real inner-product space with its Borel measurable structure and second-countable topology. Let $\mu$ be a probability measure on $E$ with finite second moment, and let
--
--   $$
--   V=\operatorname{direction}(\operatorname{affineSupport}(\mu)).
--   $$
--
--   For every nonzero $v\in V$,
--
--   $$
--   0<\left\langle
--   \operatorname{Cov}(\operatorname{intrinsicMeasure}(\mu))v,v
--   \right\rangle.
--   $$
--
--   The theorem supplies strict positivity after restricting the law to its intrinsic affine support, even when the ambient covariance may have null directions.
--
--   **Formalization Note** The finite second moment is expressed by `MemLp id 2`; no positive-dimensionality assumption is made.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Covariance/Intrinsic.lean#L181-L214 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Covariance.Intrinsic`, declaration `FunctionalInequalities.Covariance.intrinsic_operator_inner_self_pos`; the repository is private at upload time).

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
omit [CompleteSpace E]

theorem FunctionalInequalities.Covariance.intrinsic_operator_inner_self_pos_408915f (μ : ProbabilityMeasure E)
    (hμ : MemLp id 2 (μ : Measure E)) {v : (affineSupport μ).direction} (hv : v ≠ 0) :
    0 < inner ℝ (operator (intrinsicMeasure μ : Measure (affineSupport μ).direction) v) v := by sorry
