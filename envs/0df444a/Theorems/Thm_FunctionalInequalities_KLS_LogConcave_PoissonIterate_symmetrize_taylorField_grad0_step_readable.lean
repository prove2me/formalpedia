-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_symmetrize_taylorField_grad0_step_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_taylorField_grad0_step_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:56.519788+00:00
-- url     : https://prove2.me/theorems/1a522d0e-cd67-4d05-8329-16d2b2b836aa
-- title:
--   One-Step Taylor-Field Symmetrization Identity
-- statement:
--   This formalizes BKL Corollary 3.7 for one step.
--
--   Let $V$ be finite-dimensional, let $\nu=m\mathbin{.}\mathrm{tilted}(-U)$ with $U\in C^2$ and all exponential moments, and assume $C_P(\nu)\le C$. Let $h$ be a level-$k$ field and let $d\ge1$. For every coefficient index array $J$ of length $d+1+k+1$, the symmetrization over the first $d+1$ Taylor positions of the degree-$d$ Taylor field of the centered gradient of the Poisson step equals the scale times the degree-$(d+1)$ Taylor field of the centered gradient of $h$:
--
--   $$S_{d+1}T_d\bigl(\nabla_0(\operatorname{step}(h))\bigr)
--   =\operatorname{scale}(h)\,T_{d+1}(\nabla_0h).$$
--
--   The two coefficient arrays are identified through the finite-index cast specified in the formal statement.
--
--   This identity is the one-step relation iterated in the Taylor recursion.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem symmetrize_taylorField_grad0_step {k : ℕ} (h : Field ν k) {d : ℕ} (hd : 1 ≤ d)
--       (J : Fin (d + 1 + (k + 1)) → Fin (Module.finrank ℝ V)) :
--       symmetrize (Module.finrank ℝ V) (d + (k + 2)) (d + 1)
--           (taylorField d (grad0 T̄ (step T̄ h))) (J ∘ Fin.cast (by omega)) =
--         scale T̄ h * taylorField (d + 1) (grad0 T̄ h) J
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/Taylor`](https://prove2.me/theorems/4a314a0c-259a-4368-99cf-b24123869fe0).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`KLS/BKL/PoissonIterate/Basic`](https://prove2.me/theorems/d0bc548e-fc90-4f87-b06a-cf2208a1d375), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Analysis/Tensor/Coordinate`](https://prove2.me/theorems/024d1767-7544-4265-9acb-d8fe6f0df92f), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1).
--
--   Supporting theorems: [`taylorTensor_const_mul`](https://prove2.me/theorems/7da0a874-3260-449d-b383-221740a01959), [`symmetrize_apply_comp_cast`](https://prove2.me/theorems/f3dc6e21-450b-4d16-aab4-8e4451661aaa), [`taylorTensor_center`](https://prove2.me/theorems/2224e876-b11e-4fc6-980d-876a9062141d), [`taylorTensor_gen_apply`](https://prove2.me/theorems/f4cc32ce-29c2-4586-b75f-f09fd183f1c1), [`existsUnique_centered_adjointComp_eq`](https://prove2.me/theorems/52c0f77f-6c99-4a60-9925-c7dad4c02360).
--
--   Previous: [`taylorTensor_gen_apply`](https://prove2.me/theorems/f4cc32ce-29c2-4586-b75f-f09fd183f1c1) · Next: [`meanGradSq_eq_norm_taylorField_one_genField`](https://prove2.me/theorems/bb480bc9-8569-44a2-a555-12d3a5f1d619).
--
--   [Source excerpt, lines 278–282](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Taylor.lean#L278-L282) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Taylor.lean#L274-L300 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Taylor`, declaration `FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_taylorField_grad0_step`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Taylor

open FunctionalInequalities.Analysis.Tensor
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  (hexp : ∀ r : ℝ, MeasureTheory.Integrable (fun x => Real.exp (r * ‖x‖)) (ν : MeasureTheory.Measure V))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
variable {C : NNReal} (hC : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
include hνU hU hexp hC

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.symmetrize_taylorField_grad0_step_readable {k : ℕ} (h : Field ν k) {d : ℕ} (hd : 1 ≤ d)
    (J : Fin (d + 1 + (k + 1)) → Fin (Module.finrank ℝ V)) :
    symmetrize (Module.finrank ℝ V) (d + (k + 2)) (d + 1)
        (taylorField d (grad0 T̄ (step T̄ h))) (J ∘ Fin.cast (by omega)) =
      scale T̄ h * taylorField (d + 1) (grad0 T̄ h) J := by sorry
