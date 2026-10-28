-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_meanGradSq_eq_norm_taylorField_one_genField_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.meanGradSq_eq_norm_taylorField_one_genField_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:22.63682+00:00
-- url     : https://prove2.me/theorems/bb480bc9-8569-44a2-a555-12d3a5f1d619
-- title:
--   Mean Gradient Square and First Taylor Tensor
-- statement:
--   This formalizes BKL (49) for tensor fields.
--
--   Let $V$ be finite-dimensional and let $\nu=m\mathbin{.}\mathrm{tilted}(-U)$, where $U\in C^2$ and all exponential moments of $\nu$ are integrable. Let $h$ be a field at level $k$, and assume every component of $h$ belongs to the domain of $A=\bar T^\dagger\bar T$. Then the squared sum of the means of the gradient components equals the squared norm of the first Taylor field of the generator field:
--
--   $$\operatorname{meanGradSq}(h)=\left\|T_1(\operatorname{genField}(h))\right\|^2.$$
--
--   Here `meanGradSq` sums the squared norms of the component means, `genField` applies the generator componentwise, and `taylorField 1` is the corresponding first Taylor coefficient array.
--
--   This identifies the first gradient-drop quantity with a Taylor-tensor norm in the iterate analysis.
--
--   **Formalization Note:** The equality is in real numbers; all field components are $L^2(\nu)$ classes and the domain assumption is componentwise.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem meanGradSq_eq_norm_taylorField_one_genField {k : ℕ} (h : Field ν k)
--       (hh : ∀ I, h I ∈ (adjointComp T̄).domain) :
--       meanGradSq T̄ h = ‖taylorField 1 (genField T̄ h)‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/Taylor`](https://prove2.me/theorems/4a314a0c-259a-4368-99cf-b24123869fe0).
--
--   Definition modules: [`KLS/BKL/PoissonIterate/Basic`](https://prove2.me/theorems/d0bc548e-fc90-4f87-b06a-cf2208a1d375), [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Analysis/Tensor/Coordinate`](https://prove2.me/theorems/024d1767-7544-4265-9acb-d8fe6f0df92f), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Supporting theorems: [`taylorTensor_gen_apply`](https://prove2.me/theorems/f4cc32ce-29c2-4586-b75f-f09fd183f1c1).
--
--   Previous: [`symmetrize_taylorField_grad0_step`](https://prove2.me/theorems/1a522d0e-cd67-4d05-8329-16d2b2b836aa) · Next: [`sum_mean_partialDeriv_sq_le`](https://prove2.me/theorems/be8a1565-79a5-4823-bee4-b6c4a9957d96).
--
--   [Source excerpt, lines 315–317](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Taylor.lean#L315-L317) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Taylor.lean#L312-L332 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Taylor`, declaration `FunctionalInequalities.KLS.LogConcave.PoissonIterate.meanGradSq_eq_norm_taylorField_one_genField`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor

open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  (hexp : ∀ r : ℝ, MeasureTheory.Integrable (fun x => Real.exp (r * ‖x‖)) (ν : MeasureTheory.Measure V))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
include hνU hU hexp

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.meanGradSq_eq_norm_taylorField_one_genField_readable {k : ℕ} (h : Field ν k)
    (hh : ∀ I, h I ∈ (adjointComp T̄).domain) :
    meanGradSq T̄ h = ‖taylorField 1 (genField T̄ h)‖ ^ 2 := by sorry
