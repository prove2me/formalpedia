-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_seq_smooth_tendsto_adjointComp_of_localRegularity_readable
-- name    : FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp_of_localRegularity_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:30.288987+00:00
-- url     : https://prove2.me/theorems/7b48e926-80ae-40b4-a5a6-d33d9c1a1273
-- title:
--   Local Regularity Gives An Operator Core
-- statement:
--   This theorem gives an operator-core criterion from local regularity of deficiency elements.
--
--   Let $V$ be finite-dimensional and complete, let $m$ be an additive Haar measure, let $\nu$ be log-concave with nonempty interior support, and let $U\in C^1(V)$ satisfy $\nu=m.\operatorname{tilted}(-U)$. Assume that every $u\in L^2(\nu)$ satisfying
--
--   $$
--   \langle Af,u\rangle+\langle f,u\rangle=0
--   $$
--
--   for every smooth compactly supported $f$, has the property that $[\chi u]\in D(\overline{T})$ for every smooth compactly supported $\chi$, where $A=\overline{T}^{\dagger}\overline{T}$. Then every $F\in D(A)$ admits smooth compactly supported functions $f_n$ such that
--
--   $$
--   [f_n]\to F\quad\text{and}\quad A[f_n]\to AF
--   \qquad\text{in }L^2(\nu).
--   $$
--
--   In Lean, the two limits are expressed as convergence of norms to zero and the operator is `adjointComp` applied to `closedWeightedOperator`. This is an operator-core statement, not a claim about a semigroup or a curvature inequality.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_seq_smooth_tendsto_adjointComp_of_localRegularity
--       (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
--       (hreg : ∀ u : (Lp ℝ 2 (ν : Measure V)),
--         (∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
--           ⟪((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
--             ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : (Lp ℝ 2 (ν : Measure V))), u⟫ +
--             ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : (Lp ℝ 2
--               (ν : Measure V))), u⟫ = 0) →
--         ∀ (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ),
--           (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
--             (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
--       (F : ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) :
--       ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n))
--         (hfnc : ∀ n, HasCompactSupport (fn n)),
--         Tendsto (fun n => ‖(memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n)
--           - (F : (Lp ℝ 2 (ν : Measure V)))‖) atTop (𝓝 0) ∧
--         Tendsto (fun n => ‖((adjointComp
--           (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
--             ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n)
--             (hfnc n)⟩ : (Lp ℝ 2 (ν : Measure V))) - ((adjointComp
--               (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F : (Lp ℝ 2
--                 (ν : Measure V)))‖) atTop (𝓝 0)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/OperatorCore`](https://prove2.me/theorems/49f2d187-0409-49fa-a861-f4dcb4534ed2).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`KLS/LogConcave/HeatSemigroup/Generator`](https://prove2.me/theorems/1303b530-0417-4686-98e2-cba0795ab727), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Energy/WeightedGradient/Core`](https://prove2.me/theorems/f5d86bfc-b82c-47e4-a17b-d1e26078014f), [`KLS/LogConcave/WeightedGradient/Multiplier`](https://prove2.me/theorems/5b6390bb-3865-4ef0-88d2-fa41db26a901).
--
--   Supporting theorems: [`eq_zero_of_localRegularity`](https://prove2.me/theorems/51e4b343-ce48-434b-a25f-137e75ee3400).
--
--   Previous: [`eq_zero_of_localRegularity`](https://prove2.me/theorems/51e4b343-ce48-434b-a25f-137e75ee3400).
--
--   [Source excerpt, lines 716–737](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/OperatorCore.lean#L716-L737) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/OperatorCore.lean#L702-L854 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.OperatorCore`, declaration `FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp_of_localRegularity`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_OperatorCore

open MeasureTheory Filter Topology Metric Set InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
open FunctionalInequalities.Energy FunctionalInequalities.Energy.WeightedGradient
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
variable {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure]
  (hν : FunctionalInequalities.KLS.LogConcave ν) (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}

theorem FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_adjointComp_of_localRegularity_readable
    (hνU : (ν : Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 1 U)
    (hreg : ∀ u : (Lp ℝ 2 (ν : Measure V)),
      (∀ (f : V → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f),
        ⟪((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU hf hfc⟩ : (Lp ℝ 2 (ν : Measure V))), u⟫ +
          ⟪((memLp_of_contDiff_hasCompactSupport ν hf hfc).toLp f : (Lp ℝ 2
            (ν : Measure V))), u⟫ = 0) →
      ∀ (χ : V → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ),
        (memLp_mul_of_contDiff_hasCompactSupport (ν := ν) hχ hχc u).toLp _ ∈
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain)
    (F : ((adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))).domain) :
    ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n))
      (hfnc : ∀ n, HasCompactSupport (fn n)),
      Tendsto (fun n => ‖(memLp_of_contDiff_hasCompactSupport ν (hfn n) (hfnc n)).toLp (fn n)
        - (F : (Lp ℝ 2 (ν : Measure V)))‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖((adjointComp
        (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi))
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n)
          (hfnc n)⟩ : (Lp ℝ 2 (ν : Measure V))) - ((adjointComp
            (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)) F : (Lp ℝ 2
              (ν : Measure V)))‖) atTop (𝓝 0) := by sorry
