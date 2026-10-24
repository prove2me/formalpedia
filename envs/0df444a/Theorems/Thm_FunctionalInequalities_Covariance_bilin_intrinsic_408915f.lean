-- Prove2me | Theorems.Thm_FunctionalInequalities_Covariance_bilin_intrinsic_408915f
-- name    : FunctionalInequalities.Covariance.bilin_intrinsic_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:13.403345+00:00
-- url     : https://prove2.me/theorems/d2b1af0d-82d9-4660-b21d-e457378f1148
-- title:
--   Ambient and Intrinsic Covariance Bilinear Forms
-- statement:
--   This identifies the ambient covariance bilinear form with the intrinsic covariance bilinear form on the affine-support direction space.
--
--   Let $E$ be a complete, finite-dimensional, second-countable real inner-product space with its Borel measurable structure. Let $\mu$ be a probability measure on $E$ satisfying
--
--   $$
--   \operatorname{id}\in L^2(\mu).
--   $$
--
--   Let $V$ be the direction of the affine support of $\mu$, and let $v,w\in V$. Then
--
--   $$
--   \operatorname{Cov}(\operatorname{intrinsicMeasure}(\mu))(v,w)
--   =
--   \operatorname{Cov}(\mu)(v,w),
--   $$
--
--   where the right-hand side views $v,w$ as vectors in $E$.
--
--   This is the basic covariance identity for intrinsic coordinates and is reusable in comparisons between ambient and affine-support formulations.
--
--   **Formalization Note** The intrinsic law is `intrinsicMeasure μ`, and the second-moment assumption is the explicit `MemLp id 2` hypothesis.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Covariance/Intrinsic.lean#L104-L124 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Covariance.Intrinsic`, declaration `FunctionalInequalities.Covariance.bilin_intrinsic`; the repository is private at upload time).

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

theorem FunctionalInequalities.Covariance.bilin_intrinsic_408915f (μ : ProbabilityMeasure E) (hμ : MemLp id 2 (μ : Measure E))
    (v w : (affineSupport μ).direction) :
    covarianceBilin (intrinsicMeasure μ : Measure (affineSupport μ).direction) v w =
      covarianceBilin (μ : Measure E) v w := by sorry
