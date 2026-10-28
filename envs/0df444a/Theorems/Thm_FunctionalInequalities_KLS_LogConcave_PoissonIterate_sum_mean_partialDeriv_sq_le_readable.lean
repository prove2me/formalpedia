-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_sum_mean_partialDeriv_sq_le_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_mean_partialDeriv_sq_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:52.326121+00:00
-- url     : https://prove2.me/theorems/be8a1565-79a5-4823-bee4-b6c4a9957d96
-- title:
--   Mean Partial Derivative Energy Drop
-- statement:
--   This formalizes the first energy-drop estimate associated with Lemma 3.9 of Bizeul–Klartag–Lehec.
--
--   Let $V$ be a finite-dimensional real inner-product space, let $\nu$ be a log-concave probability measure with nonempty support interior, and let $m$ be an additive Haar measure. Assume all exponential moments of $\nu$ are integrable. Assume also the covariance-type bound
--   $$\int \langle v,x\rangle^2\,d\nu(x)\le\|v\|^2\qquad(v\in V).$$
--   Let $u\in L^2(\nu)$ belong to the domain of the adjoint composition of the closed weighted gradient. Then
--   $$\sum_j\left(\operatorname{mean}_\nu(\partial_j u)\right)^2
--   \le \|\operatorname{gen}(u)\|^2,$$
--   where the sum is over an orthonormal basis, `partialDeriv` denotes the coordinate derivative of the closed gradient, and `gen` denotes the generator.
--
--   The estimate controls the squared mean gradient by the generator energy and is used as the initial energy inequality in the Poisson-iterate argument.
--
--   **Formalization Note.** The domain condition is an exact domain-membership hypothesis in $L^2(\nu)$; the displayed sum is a finite-dimensional coordinate sum.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_mean_partialDeriv_sq_le
--       (hcov : ∀ v : V, ∫ x, ⟪v, x⟫ ^ 2 ∂(ν : Measure V) ≤ ‖v‖ ^ 2)
--       {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T̄).domain) :
--       ∑ j, L2.mean ν (partialDeriv T̄ j u) ^ 2 ≤ ‖gen T̄ u‖ ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/Taylor`](https://prove2.me/theorems/4a314a0c-259a-4368-99cf-b24123869fe0).
--
--   Definition modules: [`KLS/BKL/PoissonIterate/Basic`](https://prove2.me/theorems/d0bc548e-fc90-4f87-b06a-cf2208a1d375), [`L2/MeanVariance`](https://prove2.me/theorems/c46cc34a-40d9-4c7f-af02-6949935222d8), [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b).
--
--   Supporting theorems: [`exists_toLp_mem_closedWeightedOperator_domain_of_hasTemperateGrowth`](https://prove2.me/theorems/de152049-2180-4f95-9606-5806b95406d7).
--
--   Previous: [`meanGradSq_eq_norm_taylorField_one_genField`](https://prove2.me/theorems/bb480bc9-8569-44a2-a555-12d3a5f1d619).
--
--   [Source excerpt, lines 356–359](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Taylor.lean#L356-L359) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Taylor.lean#L351-L399 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Taylor`, declaration `FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_mean_partialDeriv_sq_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor

open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace ContDiff
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  (hexp : ∀ r : ℝ, MeasureTheory.Integrable (fun x => Real.exp (r * ‖x‖)) (ν : MeasureTheory.Measure V))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
include hexp

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.sum_mean_partialDeriv_sq_le_readable
    (hcov : ∀ v : V, ∫ x, ⟪v, x⟫ ^ 2 ∂(ν : Measure V) ≤ ‖v‖ ^ 2)
    {u : Lp ℝ 2 (ν : Measure V)} (hu : u ∈ (adjointComp T̄).domain) :
    ∑ j, L2.mean ν (partialDeriv T̄ j u) ^ 2 ≤ ‖gen T̄ u‖ ^ 2 := by sorry
