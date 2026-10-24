-- Prove2me | Theorems.Thm_FunctionalInequalities_Covariance_operator_map_continuousLinearEquiv_408915f
-- name    : FunctionalInequalities.Covariance.operator_map_continuousLinearEquiv_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:27:13.046899+00:00
-- url     : https://prove2.me/theorems/d8eb44ee-c979-4b67-80d0-f602d4cd7cb2
-- title:
--   Covariance Under Continuous Linear Equivalences
-- statement:
--   This describes covariance under a continuous linear equivalence.
--
--   Let $V_1$ and $V_2$ be real inner-product spaces with Borel measurable structures, assume the required completeness and second-countability conditions on $V_2$, let $\nu$ be a finite measure on $V_1$, and let
--
--   $$
--   T:V_1\overset{\sim}{\longrightarrow}V_2
--   $$
--
--   be a continuous linear equivalence. Then the covariance operator of the pushforward measure satisfies
--
--   $$
--   \operatorname{Cov}(T_\#\nu)
--   =T\circ\operatorname{Cov}(\nu)\circ T^*.
--   $$
--
--   No finite-second-moment assumption is required: when the relevant second moment is absent, the covariance operators are zero by the underlying convention.
--
--   The result is the operator conjugation law used for linear changes of variables.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Transport.lean#L293-L321 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Transport`, declaration `FunctionalInequalities.Covariance.operator_map_continuousLinearEquiv`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Transport
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Probability.Moments.CovarianceBilin

noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
universe u v
section ContinuousLinearEquiv
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]
variable (ν : ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)
variable [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂] [SecondCountableTopology V₂]
omit [SecondCountableTopology V₁]

theorem FunctionalInequalities.Covariance.operator_map_continuousLinearEquiv_408915f
    (ν : Measure V₁) [IsFiniteMeasure ν] (T : V₁ ≃L[ℝ] V₂) :
    Covariance.operator (ν.map T) =
      ((T : V₁ →L[ℝ] V₂).comp (Covariance.operator ν)).comp (T : V₁ →L[ℝ] V₂).adjoint := by sorry
