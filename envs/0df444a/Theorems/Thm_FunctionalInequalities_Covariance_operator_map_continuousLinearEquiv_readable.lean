-- Prove2me | Theorems.Thm_FunctionalInequalities_Covariance_operator_map_continuousLinearEquiv_readable
-- name    : FunctionalInequalities.Covariance.operator_map_continuousLinearEquiv_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:20.087745+00:00
-- url     : https://prove2.me/theorems/4b0ba356-0a64-4912-a8f7-67b0e65a1329
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
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem Covariance.operator_map_continuousLinearEquiv
--       (ν : Measure V₁) [IsFiniteMeasure ν] (T : V₁ ≃L[ℝ] V₂) :
--       Covariance.operator (ν.map T) =
--         ((T : V₁ →L[ℝ] V₂).comp (Covariance.operator ν)).comp (T : V₁ →L[ℝ] V₂).adjoint
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Transport`](https://prove2.me/theorems/49c9fb1d-757f-4dd4-935d-0244caf50564).
--
--   Definition modules: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc).
--
--   Previous: [`Probability.tilted_smul_pos`](https://prove2.me/theorems/082bb7e7-9916-4a6e-aaa8-68ce8d9f378f) · Next: [`Probability.affineSupport_mapContinuousLinearEquiv`](https://prove2.me/theorems/fde395de-3098-465b-b70c-cf883c0311a9).
--
--   [Source excerpt, lines 296–299](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Transport.lean#L296-L299) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Transport.lean#L293-L321 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Transport`, declaration `FunctionalInequalities.Covariance.operator_map_continuousLinearEquiv`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Transport

open MeasureTheory Filter Topology InnerProductSpace
universe u v
variable {V₁ : Type u} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
variable {V₂ : Type v} [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂]
  [MeasurableSpace V₂] [BorelSpace V₂]
variable [CompleteSpace V₁] [SecondCountableTopology V₁] [CompleteSpace V₂] [SecondCountableTopology V₂]
omit [SecondCountableTopology V₁]

theorem FunctionalInequalities.Covariance.operator_map_continuousLinearEquiv_readable
    (ν : Measure V₁) [IsFiniteMeasure ν] (T : V₁ ≃L[ℝ] V₂) :
    Covariance.operator (ν.map T) =
      ((T : V₁ →L[ℝ] V₂).comp (Covariance.operator ν)).comp (T : V₁ →L[ℝ] V₂).adjoint := by sorry
