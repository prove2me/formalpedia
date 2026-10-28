-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_exists_standardized_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.exists_standardized_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:15:15.624509+00:00
-- url     : https://prove2.me/theorems/b86ffa3f-dfc6-43a2-8cd2-8a6a6fc5a590
-- title:
--   Standardization by Covariance Whitening
-- statement:
--   This is the standardization construction for compactly supported log-concave laws.
--
--   Let $E$ be a complete finite-dimensional real inner-product space with its Borel measurable structure, and let $\mu$ be a probability measure on $E$. Assume: (1) $\mu$ is log-concave; (2) its support is compact; (3) its covariance operator $A=\operatorname{Cov}(\mu)$ is positive; and (4) $A$ is a unit, hence invertible.
--
--   Then there exist a probability measure $\eta$ and a continuous linear equivalence $W:E\simeq E$ such that
--
--   $$
--   W=A^{-1/2},\qquad \eta\text{ is isotropic, log-concave, and compactly supported},
--   $$
--
--   and
--
--   $$
--   \eta=\bigl(x\mapsto W(x-\textstyle\int y\,d\mu(y))\bigr)_\#\mu.
--   $$
--
--   The declaration packages centering and covariance whitening into an isotropic compactly supported law. It is a reduction tool and asserts existence, not uniqueness.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_standardized [CompleteSpace E] [FiniteDimensional ℝ E]
--       [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
--       (μ : ProbabilityMeasure E) (hLC : LogConcave μ)
--       (hc : IsCompact (μ : Measure E).support)
--       (hpos : (Covariance.operator (μ : Measure E)).IsPositive)
--       (hunit : IsUnit (Covariance.operator (μ : Measure E))) :
--       ∃ (η : ProbabilityMeasure E) (W : E ≃L[ℝ] E),
--         (W : E →L[ℝ] E) = inverseSqrt (Covariance.operator (μ : Measure E)) ∧
--         KLS.Isotropic η ∧ LogConcave η ∧ IsCompact (η : Measure E).support ∧
--         (η : Measure E) = (μ : Measure E).map (fun x => W (x - ∫ y, y ∂(μ : Measure E)))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/CompactReduction`](https://prove2.me/theorems/a4e51f37-ee65-417d-a309-c9c31bff2101).
--
--   Definition modules: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/Operator/InverseSqrt`](https://prove2.me/theorems/2794bd57-af01-4015-a91a-cb7827d3a533).
--
--   Supporting theorems: [`inverseSqrt_mul_mul_inverseSqrt`](https://prove2.me/theorems/88c3f67d-7fa1-4c20-b7d0-8fa8e80c182a), [`Covariance.operator_map_continuousLinearEquiv`](https://prove2.me/theorems/4b0ba356-0a64-4912-a8f7-67b0e65a1329), [`memLp_id_two`](https://prove2.me/theorems/1e1255d8-1cf4-45ef-8f96-0337bafe649e), [`of_continuousLinearEquiv_map`](https://prove2.me/theorems/c637e7db-3431-42d0-bb61-ac5baf6882b0).
--
--   Previous: [`inner_self_pos_of_norm_sub_one_lt`](https://prove2.me/theorems/3500b35b-5a79-4cfe-8a40-9807fb6246e9) · Next: [`cumulantBound_of_compact`](https://prove2.me/theorems/642ea310-0dfa-47d8-b6bd-18048856ed8f).
--
--   [Source excerpt, lines 239–248](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/CompactReduction.lean#L239-L248) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CompactReduction.lean#L236-L307 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CompactReduction`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.exists_standardized`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CompactReduction

open MeasureTheory
open Filter Topology ProbabilityTheory FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E]

theorem FunctionalInequalities.KLS.LogConcave.Suspension.exists_standardized_readable [CompleteSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : ProbabilityMeasure E) (hLC : LogConcave μ)
    (hc : IsCompact (μ : Measure E).support)
    (hpos : (Covariance.operator (μ : Measure E)).IsPositive)
    (hunit : IsUnit (Covariance.operator (μ : Measure E))) :
    ∃ (η : ProbabilityMeasure E) (W : E ≃L[ℝ] E),
      (W : E →L[ℝ] E) = inverseSqrt (Covariance.operator (μ : Measure E)) ∧
      KLS.Isotropic η ∧ LogConcave η ∧ IsCompact (η : Measure E).support ∧
      (η : Measure E) = (μ : Measure E).map (fun x => W (x - ∫ y, y ∂(μ : Measure E))) := by sorry
