-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_seq_smooth_tendsto_weakHessian_readable
-- name    : FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_weakHessian_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:17:50.193652+00:00
-- url     : https://prove2.me/theorems/710e036c-fb9b-40b7-ba2f-f65dc86dd10f
-- title:
--   Smooth Approximation for the Weak Hessian
-- statement:
--   This technical statement constructs a smooth compactly supported approximation for a generator-domain element.
--
--   Let $V$ be finite-dimensional, let $\nu=m\mathbin{.}\mathrm{tilted}(-U)$ with nonempty interior support, and assume that $U$ has temperate growth, is $C^1$, and that every exponential moment of $\nu$ is integrable. Let $\rho\in\mathbb R$ satisfy the pointwise curvature inequality
--
--   $$\rho\|v\|^2\le \nabla^2U(x)[v,v]\qquad(x,v\in V).$$
--
--   For every $F\in D(A)$, where $A=\bar T^\dagger\bar T$, there are functions $f_n\in C_c^\infty(V)$ such that:
--
--   1. $\bar T[f_n]\to\bar T F$ in $L^2(\nu)$.
--   2. $A[f_n]\to AF$ in $L^2(\nu)$.
--   3. For every standard basis vector $e_i$, the weak derivative $\langle e_i,\bar TF\rangle$ lies in the domain of $\bar T$, and $\bar T[\partial_i f_n]$ converges to $\bar T\langle e_i,\bar TF\rangle$.
--
--   This approximation lemma is used to extend smooth Hessian identities to the operator domain.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem exists_seq_smooth_tendsto_weakHessian (hνU : (ν : Measure V) = m.tilted (-U))
--       (hUt : U.HasTemperateGrowth) (hU : ContDiff ℝ 1 U)
--       (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) {ρ : ℝ}
--       (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
--       (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) :
--       ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n))
--         (hfnc : ∀ n, HasCompactSupport (fn n)),
--         Tendsto (fun n => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
--             ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi (hfn n) (hfnc n)⟩) atTop
--           (𝓝 (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
--             ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)) ∧
--         Tendsto (fun n => adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
--             ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n) (hfnc n)⟩) atTop
--           (𝓝 (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F)) ∧
--         ∀ i, ∃ h : (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
--             (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
--               ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) ∈
--             (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
--           Tendsto (fun n => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
--               ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
--                 (contDiff_fderiv_apply_infty (hfn n) (stdOrthonormalBasis ℝ V i))
--                 ((hfnc n).fderiv_apply ℝ (stdOrthonormalBasis ℝ V i))⟩) atTop
--             (𝓝 (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, h⟩))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/HeatSemigroup/Hessian`](https://prove2.me/theorems/9ec9f121-cade-4400-bbdd-811b2f170da2).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`KLS/LogConcave/HeatSemigroup/Generator`](https://prove2.me/theorems/1303b530-0417-4686-98e2-cba0795ab727), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Energy/WeightedGradient/Core`](https://prove2.me/theorems/f5d86bfc-b82c-47e4-a17b-d1e26078014f).
--
--   Supporting theorems: [`integral_hessianSq_add_le_of_hasTemperateGrowth`](https://prove2.me/theorems/fcac2fc2-d13a-43a7-b290-c7c1b8a429f0), [`tendsto_apply_of_tendsto_adjointComp`](https://prove2.me/theorems/89a4caec-afca-4ac9-a5f0-98cc15c7d63d), [`exists_seq_smooth_tendsto_adjointComp_of_localRegularity`](https://prove2.me/theorems/7b48e926-80ae-40b4-a5a6-d33d9c1a1273), [`toLp_mul_mem_closedWeightedOperator_domain_of_orthogonal`](https://prove2.me/theorems/44e63681-21ce-4775-a563-130ebf063881).
--
--   Next: [`compLp_innerSL_closedWeightedOperator_comm`](https://prove2.me/theorems/9523c342-5f06-4597-bd28-317e4e2a8f9d).
--
--   [Source excerpt, lines 265–287](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Hessian.lean#L265-L287) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/HeatSemigroup/Hessian.lean#L262-L333 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Hessian`, declaration `_private.FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Hessian.0.FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_weakHessian`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Hessian

open MeasureTheory Filter Topology InnerProductSpace
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped ContDiff RealInnerProductSpace
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}

theorem FunctionalInequalities.KLS.LogConcave.exists_seq_smooth_tendsto_weakHessian_readable (hνU : (ν : Measure V) = m.tilted (-U))
    (hUt : U.HasTemperateGrowth) (hU : ContDiff ℝ 1 U)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (ν : Measure V)) {ρ : ℝ}
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v)
    (F : (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)).domain) :
    ∃ (fn : ℕ → V → ℝ) (hfn : ∀ n, ContDiff ℝ ∞ (fn n))
      (hfnc : ∀ n, HasCompactSupport (fn n)),
      Tendsto (fun n => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi (hfn n) (hfnc n)⟩) atTop
        (𝓝 (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
          ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩)) ∧
      Tendsto (fun n => adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi)
          ⟨_, hν.toLp_mem_adjointComp_domain m hi hνU hU (hfn n) (hfnc n)⟩) atTop
        (𝓝 (adjointComp (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi) F)) ∧
      ∀ i, ∃ h : (innerSL ℝ (stdOrthonormalBasis ℝ V i)).compLp
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨(F : Lp ℝ 2 (ν : Measure V)), F.2.2⟩) ∈
          (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi).domain,
        Tendsto (fun n => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
            ⟨_, hν.toLp_mem_closedWeightedOperator_domain m hi
              (FunctionalInequalities.KLS.LogConcave.contDiff_fderiv_apply_infty (hfn n) (stdOrthonormalBasis ℝ V i))
              ((hfnc n).fderiv_apply ℝ (stdOrthonormalBasis ℝ V i))⟩) atTop
          (𝓝 (hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi ⟨_, h⟩)) := by sorry
