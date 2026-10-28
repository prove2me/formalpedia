-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_deriv_deriv_energyForm_line_readable
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.deriv_deriv_energyForm_line_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:48.792235+00:00
-- url     : https://prove2.me/theorems/8ec8d6e9-231a-4f63-b067-a5beeb835aaf
-- title:
--   Second Derivative of the Energy Form Along a Line
-- statement:
--   This statement formalizes the second-order energy-form identity associated with (88) of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $n,r\in\mathbb N$, let $T,X$ be order-$r$ coordinate tensors on $\mathbb R^n$, and let $H$ be a self-adjoint continuous linear operator on $\mathbb R^n$. Writing $M$ for its standard matrix, define
--
--   $$
--   F(\varepsilon)=\operatorname{energyForm}(I+\varepsilon H,T+\varepsilon X).
--   $$
--
--   Then
--
--   $$
--   F''(0)=2\left(
--   \|X\|^2-2\langle X,\Sigma_M T\rangle
--   +\frac12\|\Sigma_M T\|^2
--   +\frac12\sum_s\|M^{(s)}T\|^2
--   \right).
--   $$
--
--   This is the exact second derivative along the specified line and is used in the tensor energy estimates.
--
--   **Formalization Note** The tensor inner product and norms are the finite coordinate sums defined in Lean; no dimension restriction beyond $n,r\in\mathbb N$ is imposed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.CoordinateTensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem deriv_deriv_energyForm_line (T : (Fin r → Fin n) → ℝ)
--       (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hH : IsSelfAdjoint H)
--       (X : (Fin r → Fin n) → ℝ) :
--       deriv (deriv fun ε : ℝ => energyForm (1 + ε • H) (T + ε • X)) 0 =
--         2 * (inner X X - 2 * inner X (actSum (stdMatrix H) T)
--           + (1 / 2 : ℝ) * inner (actSum (stdMatrix H) T) (actSum (stdMatrix H) T)
--           + (1 / 2 : ℝ) * ∑ s, inner (actOn (stdMatrix H) s T) (actOn (stdMatrix H) s T))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/EnergyForm`](https://prove2.me/theorems/90d6c6d9-1d3c-4f3e-a98e-c4e3e5c5839e).
--
--   Definition modules: [`Analysis/Tensor/SlotAction`](https://prove2.me/theorems/ac2f7bbd-0bd0-4fc4-b26d-e658d94082e4).
--
--   Supporting theorems: [`actOn_mul`](https://prove2.me/theorems/cfa56bc5-17bf-4d9e-adde-cb98770df824), [`inner_actOn_left`](https://prove2.me/theorems/5abfdc6c-c268-4e15-8e06-33c59ea2d64e), [`inner_actSum_actSum`](https://prove2.me/theorems/af677909-39f3-405f-9380-dc4ed282eb33), [`slot_sum_two`](https://prove2.me/theorems/e0d1f1e6-4957-4586-aef5-50f1a34f8224), [`two_slot_sum`](https://prove2.me/theorems/a6830ee8-1fb6-478d-9a58-968e1fda2c6d).
--
--   Previous: [`two_slot_sum`](https://prove2.me/theorems/a6830ee8-1fb6-478d-9a58-968e1fda2c6d).
--
--   [Source excerpt, lines 883–889](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L883-L889) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L880-L1129 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.EnergyForm`, declaration `FunctionalInequalities.Analysis.CoordinateTensor.deriv_deriv_energyForm_line`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_EnergyForm

variable {n r : ℕ}
set_option maxHeartbeats 1600000

theorem FunctionalInequalities.Analysis.CoordinateTensor.deriv_deriv_energyForm_line_readable (T : (Fin r → Fin n) → ℝ)
    (H : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hH : IsSelfAdjoint H)
    (X : (Fin r → Fin n) → ℝ) :
    deriv (deriv fun ε : ℝ => energyForm (1 + ε • H) (T + ε • X)) 0 =
      2 * (inner X X - 2 * inner X (actSum (stdMatrix H) T)
        + (1 / 2 : ℝ) * inner (actSum (stdMatrix H) T) (actSum (stdMatrix H) T)
        + (1 / 2 : ℝ) * ∑ s, inner (actOn (stdMatrix H) s T) (actOn (stdMatrix H) s T)) := by sorry
