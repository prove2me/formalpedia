-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_closedWeightedOperator_id_gap_of_literature_le_readable
-- name    : FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_id_gap_of_literature_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:41.868837+00:00
-- url     : https://prove2.me/theorems/09f3e596-c3fd-4ea9-94f3-e85e0a602693
-- title:
--   Closed Unit-Gradient Gap From a Literature Poincaré Bound
-- statement:
--   This statement transfers a finite literature Poincaré bound to the domain of the closed unit gradient.
--
--   Let $V$ be a finite-dimensional complete real inner product space with its Borel measurable structure and a second-countable topology. Let $m$ be an additive Haar measure and $\nu$ a log-concave probability measure with $\operatorname{int}(\operatorname{supp}\nu)\ne\varnothing$. Set $T=$ `KLS.LogConcave.closedWeightedOperator` for $m$ and the identity weight. Assume $C\in[0,\infty)$ and $C_P^{\mathrm{lit}}(\nu)\le C$, where $C_P^{\mathrm{lit}}$ is `Poincare.LocalSlope.Intrinsic.constant`.
--
--   For every $u\in D(T)$,
--   $$
--   \|u-\operatorname{mean}_\nu(u)\mathbf1\|_{L^2(\nu)}^2
--   \le C\,\|Tu\|_{L^2(\nu;V)}^2.
--   $$
--   Here centering is `L2.center`. This provides the form-domain gap for the actual closed gradient, rather than only for smooth tests.
--
--   **Formalization Note** $C$ is `NNReal`; its `ENNReal` coercion occurs in the hypothesis, and its real coercion in the conclusion. There is no factor of $1/2$ in the squared-gradient term.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem closedWeightedOperator_id_gap_of_literature_le (C : NNReal)
--       (hC : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
--       (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
--       ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
--         (C : ℝ) * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/WeightedGradient/Poincare`](https://prove2.me/theorems/80fd6f93-3b94-490a-9376-d2fdf9e800cd).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1).
--
--   Selected supporting theorems: [`admissible_iff_memLp_gradient`](https://prove2.me/theorems/284b0183-bfda-452b-b5ff-2efd469c4a7d), [`apply_eq_norm_gradient`](https://prove2.me/theorems/aae816d4-9490-473e-9f62-e3c0294c7ffc), [`lowerSemicontinuous_sequentialRelaxation`](https://prove2.me/theorems/17428d33-0be2-4fb1-81de-28e6c75ce12e), [`sequentialRelaxation_ofLinearPMap_of_mem`](https://prove2.me/theorems/416527b0-b0d6-435c-8137-3e2f122e7c5a), [`sequentialRelaxation_ofLinearPMap_of_notMem`](https://prove2.me/theorems/e3ef01ee-0dd8-45ce-bd89-f6b6714c8f87).
--
--   [Source excerpt, lines 40–44](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Poincare.lean#L40-L44) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/WeightedGradient/Poincare.lean#L38-L67 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.WeightedGradient.Poincare`, declaration `FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_id_gap_of_literature_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_WeightedGradient_Poincare

set_option autoImplicit false
open MeasureTheory
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
  (hν : FunctionalInequalities.KLS.LogConcave ν) (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty)

theorem FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_id_gap_of_literature_le_readable (C : NNReal)
    (hC : Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
    (u : (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain) :
    ‖L2.center ν (u : Lp ℝ 2 (ν : Measure V))‖ ^ 2 ≤
      (C : ℝ) * ‖hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi u‖ ^ 2 := by sorry
