-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_PoissonIterate_grad0_step_sub_permField_succ_readable
-- name    : FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0_step_sub_permField_succ_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:41.418579+00:00
-- url     : https://prove2.me/theorems/39d622b5-c0a8-4e3a-93dc-27f25675ab33
-- title:
--   Centered Gradient Difference Under Adjacent Permutation
-- statement:
--   This formalizes BKL (42).
--
--   Let $V$ be finite-dimensional, let $\nu=m\mathbin{.}\mathrm{tilted}(-U)$ with $U\in C^2$, assume $C_P(\nu)\le C$, and let $h$ be a level-$k$ field. For an index position $\ell\in\mathrm{Fin}(k+1)$ satisfying $\ell+1<k+1$, let $\tau_\ell$ swap positions $\ell$ and $\ell+1$, and let $\tau_{\ell+1}$ be the corresponding swap after the new index is added. Then
--
--   $$\nabla_0(\operatorname{step}(h))-\tau_{\ell+1}\nabla_0(\operatorname{step}(h))
--   =\operatorname{scale}(h)\,\nabla_0(-L)^{-1}\bigl(\nabla_0h-\tau_\ell\nabla_0h\bigr).$$
--
--   The permutations are represented by `permField` using `Equiv.swap` and `finRotate`.
--
--   This identity propagates approximate symmetry from one iterate to the next.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.PoissonIterate`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem grad0_step_sub_permField_succ {k : ℕ} (h : Field ν k) (ℓ : Fin (k + 1))
--       (hℓ : ℓ.val + 1 < k + 1) :
--       grad0 T̄ (step T̄ h) -
--           permField (Equiv.swap ℓ.succ (finRotate (k + 2) ℓ.succ)) (grad0 T̄ (step T̄ h)) =
--         scale T̄ h • grad0 T̄ (invField T̄
--           (grad0 T̄ h - permField (Equiv.swap ℓ (finRotate (k + 1) ℓ)) (grad0 T̄ h)))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/PoissonIterate/Symmetry`](https://prove2.me/theorems/39390486-c6df-45a6-82e9-cb779c8b05f8).
--
--   Definition modules: [`KLS/LogConcave/WeightedGradient/Closure`](https://prove2.me/theorems/5e48f798-42aa-4f04-9631-b91b826d06f2), [`KLS/BKL/PoissonIterate/Basic`](https://prove2.me/theorems/d0bc548e-fc90-4f87-b06a-cf2208a1d375), [`Probability/LogConcave`](https://prove2.me/theorems/806cd3df-b03f-48fa-a2e4-4711229a309b), [`Poincare/LocalSlope/Basic`](https://prove2.me/theorems/4e65eb6a-acd3-4142-85a9-b5d14c62f3d1).
--
--   Supporting theorems: [`grad0_sub`](https://prove2.me/theorems/4388ae07-53e8-4f4c-88d5-4b286c971585), [`existsUnique_centered_adjointComp_eq`](https://prove2.me/theorems/52c0f77f-6c99-4a60-9925-c7dad4c02360).
--
--   Previous: [`grad0_sub`](https://prove2.me/theorems/4388ae07-53e8-4f4c-88d5-4b286c971585) · Next: [`normSq_grad0_iter_sub_symField_le`](https://prove2.me/theorems/d2595a15-dab4-4dcb-8911-a565f24e2eee).
--
--   [Source excerpt, lines 191–196](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Symmetry.lean#L191-L196) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Symmetry.lean#L187-L207 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Symmetry`, declaration `FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0_step_sub_permField_succ`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Symmetry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {ν : MeasureTheory.ProbabilityMeasure V} (m : MeasureTheory.Measure V) [m.IsAddHaarMeasure] (hν : FunctionalInequalities.KLS.LogConcave ν)
  (hi : (interior (ν : MeasureTheory.Measure V).support).Nonempty) {U : V → ℝ}
  (hνU : (ν : MeasureTheory.Measure V) = m.tilted (-U)) (hU : ContDiff ℝ 2 U)
  {C : NNReal} (hC : FunctionalInequalities.Poincare.LocalSlope.Intrinsic.constant ν ≤ (C : ENNReal))
local notation "T̄" => hν.closedWeightedOperator m (ContinuousLinearMap.id ℝ V) hi
include hνU hU hC

theorem FunctionalInequalities.KLS.LogConcave.PoissonIterate.grad0_step_sub_permField_succ_readable {k : ℕ} (h : Field ν k) (ℓ : Fin (k + 1))
    (hℓ : ℓ.val + 1 < k + 1) :
    grad0 T̄ (step T̄ h) -
        permField (Equiv.swap ℓ.succ (finRotate (k + 2) ℓ.succ)) (grad0 T̄ (step T̄ h)) =
      scale T̄ h • grad0 T̄ (invField T̄
        (grad0 T̄ h - permField (Equiv.swap ℓ (finRotate (k + 1) ℓ)) (grad0 T̄ h))) := by sorry
