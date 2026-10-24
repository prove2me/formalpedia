-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_affineSupport_mapContinuousLinearEquiv_408915f
-- name    : FunctionalInequalities.Probability.affineSupport_mapContinuousLinearEquiv_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:24:26.361299+00:00
-- url     : https://prove2.me/theorems/ae14d33e-33d1-47b5-9cc4-90d48fad163d
-- title:
--   Affine Support Under A Continuous Linear Equivalence
-- statement:
--   This theorem describes the affine support of a pushforward probability law.
--
--   Let $V_1$ and $V_2$ be normed real inner-product spaces with measurable Borel structures, let $\nu$ be a probability measure on $V_1$, and let $T:V_1\to V_2$ be a continuous linear equivalence. Assume the second-countable and finite-dimensional hypotheses stated in the type. Then
--
--   $$
--   \operatorname{affineSupport}(T_\#\nu)
--   =
--   T\bigl(\operatorname{affineSupport}(\nu)\bigr),
--   $$
--
--   where the image on the right is the affine-subspace map induced by the linear equivalence. In Lean, the pushforward is `mapContinuousLinearEquiv` and the affine-subspace image is formed with `AffineSubspace.map`. This is a transport lemma for affine support and does not assert anything about covariance or moments.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Transport.lean#L376-L396 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Transport`, declaration `FunctionalInequalities.Probability.affineSupport_mapContinuousLinearEquiv`; the repository is private at upload time).

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
variable [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]
omit [CompleteSpace V₁] [CompleteSpace V₂] [FiniteDimensional ℝ V₁]

theorem FunctionalInequalities.Probability.affineSupport_mapContinuousLinearEquiv_408915f :
    affineSupport (mapContinuousLinearEquiv ν T) = (affineSupport ν).map (T : V₁ →ₗ[ℝ] V₂).toAffineMap := by sorry
