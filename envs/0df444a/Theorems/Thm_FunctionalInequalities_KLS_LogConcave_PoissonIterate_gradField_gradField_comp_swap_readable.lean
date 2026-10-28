-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_gradField_gradField_comp_swap_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField_gradField_comp_swap_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:30.825327+00:00
-- url     : https://prove2.me/theorems/fe934d26-fd02-40db-8ef8-1bccbedf2dca
-- title:
--   Symmetry of the Indexed Weak Hessian
-- statement:
--   This statement proves symmetry of the first two indices of an indexed weak Hessian.
--
--   Let $V$ be finite-dimensional, let $\nu=m\mathbin{.}\mathrm{tilted}(-U)$ with $U$ of temperate growth and all exponential moments, and let $h$ be a level-$k$ field whose components lie in the domain of $A=\bar T^\dagger\bar T$. For every index map $J:\mathrm{Fin}(k+2)\to\mathrm{Fin}(\dim V)$, swapping the first two positions leaves the iterated gradient field unchanged:
--
--   $$\operatorname{gradField}(\operatorname{gradField}(h))(J\circ(0\;1))
--   =\operatorname{gradField}(\operatorname{gradField}(h))(J).$$
--
--   This is the coordinate symmetry needed to construct symmetric approximations to centered gradient fields.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem gradField_gradField_comp_swap {k : ℕ} (h : Field ν k)
--       (hh : ∀ I, h I ∈ (adjointComp T̄).domain)
--       (J : Fin (k + 2) → Fin (Module.finrank ℝ V)) :
--       gradField T̄ (gradField T̄ h) (J ∘ Equiv.swap 0 1) = gradField T̄ (gradField T̄ h) J
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/Defect`](https://prove2.me/theorems/d0aba350-4ee9-4d0f-afbf-76da9501de4e).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`KLS/BKL/PoissonIterate/Basic`](https://prove2.me/theorems/d0bc548e-fc90-4f87-b06a-cf2208a1d375), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Supporting theorems: [`compLp_innerSL_closedWeightedOperator_comm`](https://prove2.me/theorems/9523c342-5f06-4597-bd28-317e4e2a8f9d), [`convexOn_of_eq_tilted`](https://prove2.me/theorems/c25e8adc-034c-4eda-8eb4-4a844cb9f0fc), [`exists_seq_smooth_tendsto_weakHessian`](https://prove2.me/theorems/710e036c-fb9b-40b7-ba2f-f65dc86dd10f).
--
--   Previous: [`normSq_gradField_gradField_step`](https://prove2.me/theorems/c3635e07-b5fc-495e-8c70-9fdff190dfa0) · Next: [`exists_symm_normSq_grad0_step_sub_le`](https://prove2.me/theorems/ba72328f-adc1-4c83-8563-da6a4a0c7a49).
--
--   [Source excerpt, lines 252–255](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Defect.lean#L252-L255) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Defect.lean#L249-L267 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Defect`, declaration `FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField_gradField_comp_swap`; the repository is private at upload time).

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
include hνU hUt hexp

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.gradField_gradField_comp_swap_readable {k : ℕ} (h : Field ν k)
    (hh : ∀ I, h I ∈ (adjointComp T̄).domain)
    (J : Fin (k + 2) → Fin (Module.finrank ℝ V)) :
    gradField T̄ (gradField T̄ h) (J ∘ Equiv.swap 0 1) = gradField T̄ (gradField T̄ h) J := by sorry
