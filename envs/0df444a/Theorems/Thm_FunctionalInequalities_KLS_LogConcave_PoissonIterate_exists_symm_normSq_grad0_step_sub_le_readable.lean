-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_exists_symm_normSq_grad0_step_sub_le_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.exists_symm_normSq_grad0_step_sub_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:13.241284+00:00
-- url     : https://prove2.me/theorems/ba72328f-adc1-4c83-8563-da6a4a0c7a49
-- title:
--   Symmetric Approximation of a Centered Gradient Step
-- statement:
--   This formalizes BKL Lemma 3.2 for one step.
--
--   Let $V$ be finite-dimensional, let $\nu=m\mathbin{.}\mathrm{tilted}(-U)$ with $U$ of temperate growth and all exponential moments, and suppose $C_P(\nu)\le C$ with $C>0$. Let $h$ be a level-$k$ field whose components lie in $D(A)$, where $A=\bar T^\dagger\bar T$. Then there exists a level-$(k+2)$ field $S$ such that:
--
--   1. $S$ is symmetric in its first two indices:
--      $$S(J\circ(0\;1))=S(J).$$
--   2. The centered gradient of the Poisson step is within the defect bound:
--      $$\|\nabla_0(\operatorname{step}(h))-S\|^2\le C\,\operatorname{defect}(h).$$
--
--   The field $S$ is allowed to depend on $h$ and is not asserted to be unique.
--
--   This estimate is the starting point for the approximate symmetry bounds of later iterates.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_symm_normSq_grad0_step_sub_le (hCpos : 0 < C) {k : ℕ} (h : Field ν k)
--       (hh : ∀ I, h I ∈ (adjointComp T̄).domain) :
--       ∃ S : Field ν (k + 2), (∀ J, S (J ∘ Equiv.swap 0 1) = S J) ∧
--         normSq (grad0 T̄ (step T̄ h) - S) ≤ (C : ℝ) * defect T̄ h
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/Defect`](https://prove2.me/theorems/d0aba350-4ee9-4d0f-afbf-76da9501de4e).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`KLS/BKL/PoissonIterate/Basic`](https://prove2.me/theorems/d0bc548e-fc90-4f87-b06a-cf2208a1d375), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1).
--
--   Supporting theorems: [`gradField_gradField_comp_swap`](https://prove2.me/theorems/fe934d26-fd02-40db-8ef8-1bccbedf2dca), [`inv_le_scale_sq_step`](https://prove2.me/theorems/f9eabf78-c00a-4ef8-a681-0262f5a3b540), [`inner_center_center`](https://prove2.me/theorems/abb6082d-7b62-4620-a9a1-7ab8a33a4366), [`sum_norm_sq_compLp_innerSL`](https://prove2.me/theorems/886e463b-28f3-4769-9471-649161462a00).
--
--   Previous: [`gradField_gradField_comp_swap`](https://prove2.me/theorems/fe934d26-fd02-40db-8ef8-1bccbedf2dca).
--
--   [Source excerpt, lines 285–288](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Defect.lean#L285-L288) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Defect.lean#L281-L309 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Defect`, declaration `FunctionalInequalities.KLS.LogConcave.PoissonIterate.exists_symm_normSq_grad0_step_sub_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Defect

open FunctionalInequalities.Analysis.Semigroup
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hUt : U.HasTemperateGrowth)
  (hexp : ∀ r : ℝ, MeasureTheory.Integrable (fun x => Real.exp (r * ‖x‖)) (ν : MeasureTheory.Measure V))
  {C : NNReal} (hC : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
include hνU hUt hexp hC

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.exists_symm_normSq_grad0_step_sub_le_readable (hCpos : 0 < C) {k : ℕ} (h : Field ν k)
    (hh : ∀ I, h I ∈ (adjointComp T̄).domain) :
    ∃ S : Field ν (k + 2), (∀ J, S (J ∘ Equiv.swap 0 1) = S J) ∧
      normSq (grad0 T̄ (step T̄ h) - S) ≤ (C : ℝ) * defect T̄ h := by sorry
