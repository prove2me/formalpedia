-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_affineSupport_mapContinuousLinearEquiv_readable
-- name    : FunctionalInequalities.Probability.affineSupport_mapContinuousLinearEquiv_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:06.283033+00:00
-- url     : https://prove2.me/theorems/fde395de-3098-465b-b70c-cf883c0311a9
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
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem Probability.affineSupport_mapContinuousLinearEquiv :
--       affineSupport (mapContinuousLinearEquiv ν T) = (affineSupport ν).map (T : V₁ →ₗ[ℝ] V₂).toAffineMap
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Transport`](https://prove2.me/theorems/49c9fb1d-757f-4dd4-935d-0244caf50564).
--
--   Definition modules: [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81).
--
--   Previous: [`Covariance.operator_map_continuousLinearEquiv`](https://prove2.me/theorems/4b0ba356-0a64-4912-a8f7-67b0e65a1329).
--
--   [Source excerpt, lines 378–379](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Transport.lean#L378-L379) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Transport.lean#L376-L396 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Transport`, declaration `FunctionalInequalities.Probability.affineSupport_mapContinuousLinearEquiv`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport

universe u v
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]
variable (ν : MeasureTheory.ProbabilityMeasure V₁) (T : V₁ ≃L[ℝ] V₂)
variable [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂] [SecondCountableTopology V₂]
variable [FiniteDimensional ℝ V₁] [FiniteDimensional ℝ V₂]
omit [CompleteSpace V₁] [CompleteSpace V₂] [FiniteDimensional ℝ V₁]

theorem FunctionalInequalities.Probability.affineSupport_mapContinuousLinearEquiv_readable :
    affineSupport (mapContinuousLinearEquiv ν T) = (affineSupport ν).map (T : V₁ →ₗ[ℝ] V₂).toAffineMap := by sorry
