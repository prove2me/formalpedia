-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_closedWeightedOperator_one_eq_zero_readable
-- name    : FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_one_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:23.435694+00:00
-- url     : https://prove2.me/theorems/a397e39c-598f-4ce0-b673-0b4857eee9cf
-- title:
--   The Closed Weighted Gradient Annihilates One
-- statement:
--   This statement asserts that the constant-one vector is annihilated by the closed weighted gradient.
--
--   Let $V$ be a finite-dimensional complete real inner product space with its Borel measurable structure and a second-countable topology. Let $m$ be an additive Haar measure, $B:V\to V$ a continuous linear map, and $\nu$ a log-concave probability measure with nonempty interior of its support. Let $T=$ `KLS.LogConcave.closedWeightedOperator` with weight $B$ and Haar measure $m$.
--
--   For the constant-one $L^2(\nu)$ vector $\mathbf1=$ `L2.const ν 1`, equipped with its certified membership in $D(T)$,
--   $$
--   T\mathbf1=0.
--   $$
--   This supplies the constant-one kernel identity used in operator and semigroup formulations.
--
--   **Formalization Note** Domain membership is supplied by `one_mem_domain_closedWeightedOperator`. The equality is in the vector-valued $L^2$ target, hence concerns equivalence classes rather than a pointwise representative. No invertibility assumption on $B$ is imposed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem closedWeightedOperator_one_eq_zero (hν : LogConcave ν)
--       (hi : (interior (ν : Measure V).support).Nonempty) :
--       hν.closedWeightedOperator m B hi
--           ⟨L2.const ν 1, one_mem_domain_closedWeightedOperator m B hν hi⟩ = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/Markov`](https://prove2.me/theorems/73466029-c8a0-4ff1-b09b-fd66281b152c).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8).
--
--   [Source excerpt, lines 233–236](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Markov.lean#L233-L236) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Markov.lean#L232-L253 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Markov`, declaration `FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_one_eq_zero`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Markov

open Filter InnerProductSpace MeasureTheory Topology
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (B : V →L[ℝ] V)

theorem FunctionalInequalities.KLS.LogConcave.closedWeightedOperator_one_eq_zero_readable (hν : LogConcave ν)
    (hi : (interior (ν : Measure V).support).Nonempty) :
    hν.closedWeightedOperator m B hi
        ⟨L2.const ν 1, one_mem_domain_closedWeightedOperator m B hν hi⟩ = 0 := by sorry
