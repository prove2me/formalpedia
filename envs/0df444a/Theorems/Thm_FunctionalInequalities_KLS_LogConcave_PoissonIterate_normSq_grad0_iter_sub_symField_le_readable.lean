-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_normSq_grad0_iter_sub_symField_le_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_grad0_iter_sub_symField_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:45.938542+00:00
-- url     : https://prove2.me/theorems/d2595a15-dab4-4dcb-8911-a565f24e2eee
-- title:
--   Approximate Symmetry of Poisson Iterates
-- statement:
--   This formalizes BKL Lemma 3.3, p. 12.
--
--   Let $V$ be finite-dimensional, let $\nu=m\mathbin{.}\mathrm{tilted}(-U)$ with $U$ of temperate growth and all exponential moments, and assume $C_P(\nu)\le C$ with $C>0$. Let $f\in D(A)$, where $A=\bar T^\dagger\bar T$. For natural numbers $k,q$ and a real $\beta$, assume:
--
--   1. $2\le q\le k+1$.
--   2. For every $j$ with $k+1-q\le j<k$, the iterate scale satisfies
--      $$0<\alpha_j,\qquad \alpha_j^2\le\frac\beta C.$$
--
--   Then the centered gradient field of the $k$th iterate obeys
--
--   $$\|\nabla_0h_{k+1}-S_q\nabla_0h_{k+1}\|^2
--   \le4q^4\max(1,\beta)^qC
--   \sum_{j=k+1-q}^{k-1}\chi_j,$$
--
--   where $S_q$ symmetrizes the first $q$ positions and $\chi_j$ is the defect of the corresponding iterate.
--
--   This is the main approximate-symmetry estimate used in the Taylor recursion.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem normSq_grad0_iter_sub_symField_le (hCpos : 0 < C)
--       {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp T̄).domain) {β : ℝ} (k q : ℕ)
--       (hq : 2 ≤ q) (hqk : q ≤ k + 1)
--       (hα : ∀ j, k + 1 - q ≤ j → j < k →
--         0 < scale T̄ (iter T̄ f j) ∧ scale T̄ (iter T̄ f j) ^ 2 ≤ β / C) :
--       normSq (grad0 T̄ (iter T̄ f k) - symField q (grad0 T̄ (iter T̄ f k))) ≤
--         4 * (q : ℝ) ^ 4 * max 1 β ^ q * C *
--           ∑ j ∈ Finset.Ico (k + 1 - q) k, defect T̄ (iter T̄ f j)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/Symmetry`](https://prove2.me/theorems/39390486-c6df-45a6-82e9-cb779c8b05f8).
--
--   Definition modules: [`KLS/BKL/PoissonIterate/Basic`](https://prove2.me/theorems/d0bc548e-fc90-4f87-b06a-cf2208a1d375), [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`Analysis/Semigroup/AdjointComp`](https://prove2.me/theorems/6866b968-f1b9-4dde-afcb-6300d5a7a48a), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1).
--
--   Selected supporting theorems: [`exists_symm_normSq_grad0_step_sub_le`](https://prove2.me/theorems/ba72328f-adc1-4c83-8563-da6a4a0c7a49), [`grad0_step_sub_permField_succ`](https://prove2.me/theorems/39d622b5-c0a8-4e3a-93dc-27f25675ab33), [`normSq_sub_symField_le`](https://prove2.me/theorems/76359b53-6bf9-43ab-bb7a-bc9a40372a88), [`centered_adjointComp_bounds`](https://prove2.me/theorems/ec846df1-cd32-4ff0-8f0d-472ede37aec2), [`existsUnique_centered_adjointComp_eq`](https://prove2.me/theorems/52c0f77f-6c99-4a60-9925-c7dad4c02360).
--
--   Previous: [`grad0_step_sub_permField_succ`](https://prove2.me/theorems/39d622b5-c0a8-4e3a-93dc-27f25675ab33).
--
--   [Source excerpt, lines 349–356](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Symmetry.lean#L349-L356) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Lemma 3.3, p. 12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Symmetry.lean#L345-L373 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Symmetry`, declaration `FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_grad0_iter_sub_symField_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Symmetry

open MeasureTheory Finset
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

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.normSq_grad0_iter_sub_symField_le_readable (hCpos : 0 < C)
    {f : Lp ℝ 2 (ν : Measure V)} (hf : f ∈ (adjointComp T̄).domain) {β : ℝ} (k q : ℕ)
    (hq : 2 ≤ q) (hqk : q ≤ k + 1)
    (hα : ∀ j, k + 1 - q ≤ j → j < k →
      0 < scale T̄ (iter T̄ f j) ∧ scale T̄ (iter T̄ f j) ^ 2 ≤ β / C) :
    normSq (grad0 T̄ (iter T̄ f k) - symField q (grad0 T̄ (iter T̄ f k))) ≤
      4 * (q : ℝ) ^ 4 * max 1 β ^ q * C *
        ∑ j ∈ Finset.Ico (k + 1 - q) k, defect T̄ (iter T̄ f j) := by sorry
