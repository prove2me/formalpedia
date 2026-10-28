-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_normSq_gradField_gradField_step_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_gradField_gradField_step_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:38.936313+00:00
-- url     : https://prove2.me/theorems/c3635e07-b5fc-495e-8c70-9fdff190dfa0
-- title:
--   One-Step Hessian Defect Decomposition
-- statement:
--   This formalizes BKL (47) for one Poisson step.
--
--   Let $V$ be finite-dimensional, let $\nu=m\mathbin{.}\mathrm{tilted}(-U)$ with $U$ of temperate growth and all exponential moments, and assume $C_P(\nu)\le C$. Let $h$ be a field whose components lie in the domain of $A=\bar T^\dagger\bar T$. Let $h'=\operatorname{step}(h)=\alpha(-L)^{-1}\nabla_0h$, where $\alpha=\operatorname{scale}(h)$. Then
--
--   $$\|\nabla^2h\|^2=\|Lh'\|^2+\|\nabla^2h-\alpha\nabla h'\|^2.$$
--
--   In the formalization, the final term is `defect h`, `genField (step h)` represents the generator field, and `normSq` is the squared Hilbert–Schmidt norm of the indexed field.
--
--   This Pythagorean identity is the basic one-step energy relation behind the defect estimates.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem normSq_gradField_gradField_step {k : ℕ} (h : Field ν k)
--       (hh : ∀ I, h I ∈ (adjointComp T̄).domain) :
--       normSq (gradField T̄ (gradField T̄ h)) = normSq (genField T̄ (step T̄ h)) + defect T̄ h
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/Defect`](https://prove2.me/theorems/d0aba350-4ee9-4d0f-afbf-76da9501de4e).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`KLS/BKL/PoissonIterate/Basic`](https://prove2.me/theorems/d0bc548e-fc90-4f87-b06a-cf2208a1d375), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1).
--
--   Selected supporting theorems: [`closedWeightedOperator_id_gap_of_literature_le`](https://prove2.me/theorems/09f3e596-c3fd-4ea9-94f3-e85e0a602693), [`convexOn_of_eq_tilted`](https://prove2.me/theorems/c25e8adc-034c-4eda-8eb4-4a844cb9f0fc), [`existsUnique_centered_adjointComp_eq`](https://prove2.me/theorems/52c0f77f-6c99-4a60-9925-c7dad4c02360), [`inner_center_center`](https://prove2.me/theorems/abb6082d-7b62-4620-a9a1-7ab8a33a4366), [`sum_norm_sq_compLp_innerSL`](https://prove2.me/theorems/886e463b-28f3-4769-9471-649161462a00).
--
--   Next: [`gradField_gradField_comp_swap`](https://prove2.me/theorems/fe934d26-fd02-40db-8ef8-1bccbedf2dca).
--
--   [Source excerpt, lines 185–187](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Defect.lean#L185-L187) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Defect.lean#L182-L214 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Defect`, declaration `FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_gradField_gradField_step`; the repository is private at upload time).

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

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_gradField_gradField_step_readable {k : ℕ} (h : Field ν k)
    (hh : ∀ I, h I ∈ (adjointComp T̄).domain) :
    normSq (gradField T̄ (gradField T̄ h)) = normSq (genField T̄ (step T̄ h)) + defect T̄ h := by sorry
