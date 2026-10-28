-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_isotropic_localSlope_constant_eq_readable
-- name    : FunctionalInequalities.KLS.LogConcave.exists_isotropic_localSlope_constant_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:09.706043+00:00
-- url     : https://prove2.me/theorems/5dfc02d9-caf9-4e32-9ec6-e921e0672aed
-- title:
--   Isotropic Log-Concave Reduction with Equal Intrinsic Constant
-- statement:
--   This is the isotropic reduction for a log-concave law.
--
--   Let $E$ be a finite-dimensional real inner-product normed space with Borel and second-countable structure, and let $\mu$ be a log-concave probability measure on $E$. Then there exists a probability measure $\nu'$ on the direction space of $\operatorname{affineSupport}(\mu)$ such that:
--
--   1. $\nu'$ is log-concave;
--   2. $\nu'$ is isotropic, including finite second moment, zero mean, and identity covariance operator;
--   3. the intrinsic covariance-gradient Poincaré constant of $\mu$ equals the intrinsic local-slope constant of $\nu'$:
--   $$C_P^{\mathrm{Cov},\mathrm{intr}}(\mu)=C_P^{\mathrm{LocalSlope},\mathrm{intr}}(\nu').$$
--
--   The conclusion is existential and may place $\nu'$ on a lower-dimensional affine direction space; it does not assert finiteness of the common constant.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_isotropic_localSlope_constant_eq {μ : ProbabilityMeasure E}
--       (hμ : LogConcave μ) :
--       ∃ ν' : ProbabilityMeasure (affineSupport μ).direction,
--         LogConcave ν' ∧ Isotropic ν' ∧ Poincare.CovarianceGradient.Intrinsic.constant μ = Poincare.LocalSlope.Intrinsic.constant ν'
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Isotropic`](https://prove2.me/theorems/35471368-b77f-4600-8554-699e6845e252).
--
--   Definition modules: [`Poincare/CovarianceGradient/Intrinsic`](https://prove2.me/theorems/1f8dcbca-2143-4720-b0ae-d14854806427), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Probability/AffineSupport`](https://prove2.me/theorems/94abfb4a-13e9-434c-bb03-f6b05ced8e81), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1).
--
--   Selected supporting theorems: [`intrinsic_operator_inner_self_pos`](https://prove2.me/theorems/af1259be-6217-4dce-8a0d-ab64ed2f22cf), [`Covariance.operator_map_continuousLinearEquiv`](https://prove2.me/theorems/4b0ba356-0a64-4912-a8f7-67b0e65a1329), [`relaxation_eq_ofLinearPMap`](https://prove2.me/theorems/ecd8db80-1079-4c3b-8976-dc3390ed944f), [`relaxation_mapContinuousLinearEquiv`](https://prove2.me/theorems/57355011-3577-4382-8bb8-e203da4929a1), [`relaxation_translateLaw`](https://prove2.me/theorems/b4c355ab-cc76-40d6-94c9-673aabcb6e41).
--
--   Previous: [`of_continuousLinearEquiv_map`](https://prove2.me/theorems/c637e7db-3431-42d0-bb61-ac5baf6882b0) · Next: [`localSlope_le_mul_intrinsicCovariance`](https://prove2.me/theorems/102edef9-2afb-4d6f-8f68-c39def16f9cf).
--
--   [Source excerpt, lines 199–202](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean#L199-L202) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Isotropic.lean#L195-L252 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Isotropic`, declaration `FunctionalInequalities.KLS.LogConcave.exists_isotropic_localSlope_constant_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Isotropic

open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean FunctionalInequalities.Probability
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]
omit [CompleteSpace E]

theorem FunctionalInequalities.KLS.LogConcave.exists_isotropic_localSlope_constant_eq_readable {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) :
    ∃ ν' : ProbabilityMeasure (affineSupport μ).direction,
      LogConcave ν' ∧ Isotropic ν' ∧ Poincare.CovarianceGradient.Intrinsic.constant μ = Poincare.LocalSlope.Intrinsic.constant ν' := by sorry
