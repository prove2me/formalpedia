-- Prove2me | Theorems.Thm_FunctionalInequalities_Energy_CovarianceGradient_relaxation_mapContinuousLinearEquiv_readable
-- name    : FunctionalInequalities.Energy.CovarianceGradient.relaxation_mapContinuousLinearEquiv_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:25.34402+00:00
-- url     : https://prove2.me/theorems/57355011-3577-4382-8bb8-e203da4929a1
-- title:
--   Covariance Relaxation Under Linear Equivalence
-- statement:
--   This proves covariance-relaxation invariance under a continuous linear equivalence.
--
--   Let $V_1,V_2$ be complete real inner-product spaces with Borel measurable structures, let $\nu$ be a probability measure on $V_1$, let
--
--   $$
--   T:V_1\overset{\sim}{\longrightarrow}V_2
--   $$
--
--   be a continuous linear equivalence, and let $f\in L^2(T_\#\nu)$. Then
--
--   $$
--   \operatorname{relaxation}(T_\#\nu)(f)
--   =
--   \operatorname{relaxation}(\nu)(T^*f),
--   $$
--
--   where $T^*f$ denotes the pullback of $f$ through the induced $L^2$ equivalence, represented in Lean by `L2.ContinuousLinearEquiv.pullbackEquiv ν T`.
--
--   The statement expresses covariance-energy invariance under arbitrary invertible linear coordinate changes.
--
--   **Formalization Note** Finite-dimensionality and second-countability of the source are not required by the declaration; the target has the stated second-countability assumption.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Energy.CovarianceGradient`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem relaxation_mapContinuousLinearEquiv (f : Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂)) :
--       relaxation (Probability.mapContinuousLinearEquiv ν T) f = relaxation ν (L2.ContinuousLinearEquiv.pullbackEquiv ν T f)
--   ```
--
--   **Module navigation**
--
--   Module: [`Energy/CovarianceGradient/LinearEquiv`](https://prove2.me/theorems/3edabcc8-b48c-4028-8b8e-560f716da5f0).
--
--   Definition modules: [`L2/Transport`](https://prove2.me/theorems/18833b5b-77e3-4a08-986b-55e8c2b513b7), [`Energy/Form/Functional`](https://prove2.me/theorems/4dfa9356-1019-4d47-ba3e-299615584765), [`Probability/Transport`](https://prove2.me/theorems/49c9fb1d-757f-4dd4-935d-0244caf50564), [`Energy/CovarianceGradient/Basic`](https://prove2.me/theorems/517395bc-0a9a-4b82-b89c-ca3b5281db43).
--
--   Supporting theorems: [`Covariance.operator_map_continuousLinearEquiv`](https://prove2.me/theorems/4b0ba356-0a64-4912-a8f7-67b0e65a1329).
--
--   [Source excerpt, lines 151–152](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Energy/CovarianceGradient/LinearEquiv.lean#L151-L152) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Energy/CovarianceGradient/LinearEquiv.lean#L147-L179 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Energy.CovarianceGradient.LinearEquiv`, declaration `FunctionalInequalities.Energy.CovarianceGradient.relaxation_mapContinuousLinearEquiv`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Energy_CovarianceGradient_LinearEquiv

open MeasureTheory Filter Topology InnerProductSpace
universe u v
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [CompleteSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [CompleteSpace V₂]
variable [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁] [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂]
variable (ν : MeasureTheory.ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)
omit [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]
omit [SecondCountableTopology V₁]

theorem FunctionalInequalities.Energy.CovarianceGradient.relaxation_mapContinuousLinearEquiv_readable (f : Lp ℝ 2 (Probability.mapContinuousLinearEquiv ν T : Measure V₂)) :
    relaxation (Probability.mapContinuousLinearEquiv ν T) f = relaxation ν (L2.ContinuousLinearEquiv.pullbackEquiv ν T f) := by sorry
