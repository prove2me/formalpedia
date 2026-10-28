-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_CoordinateTensor_contDiffAt_energyForm_readable
-- name    : FunctionalInequalities.Analysis.CoordinateTensor.contDiffAt_energyForm_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:42.255783+00:00
-- url     : https://prove2.me/theorems/3ecc6a67-dc0c-4de0-aced-f227c0a5133b
-- title:
--   Smoothness of the Energy Form Near Invertible Operators
-- statement:
--   This statement proves that the coordinate-tensor energy form is $C^2$ near an invertible operator.
--
--   Let $n,r\in\mathbb N$, let $A$ be a continuous linear operator on $\mathbb R^n$ represented as `EuclideanSpace ℝ (Fin n)`, and assume $A$ is a unit, hence invertible in the relevant operator ring. Let $T:(\operatorname{Fin}(r)\to\operatorname{Fin}(n))\to\mathbb R$. Then the map
--
--   $$
--   (A',T')\longmapsto \operatorname{energyForm}(A',T')
--   $$
--
--   is twice continuously differentiable at $(A,T)$.
--
--   This local regularity result supplies the differentiability needed for second-order calculations involving the energy form.
--
--   **Formalization Note** The statement uses finite-dimensional `EuclideanSpace ℝ (Fin n)` and Lean's `IsUnit` hypothesis rather than a separately stated determinant condition.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.CoordinateTensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem contDiffAt_energyForm (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsUnit A)
--       (T : (Fin r → Fin n) → ℝ) :
--       ContDiffAt ℝ 2 (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × ((Fin r → Fin n) → ℝ) =>
--         energyForm q.1 q.2) (A, T)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/EnergyForm`](https://prove2.me/theorems/90d6c6d9-1d3c-4f3e-a98e-c4e3e5c5839e).
--
--   Next: [`sum_mul_prod_delta_erase`](https://prove2.me/theorems/3d2d4761-884a-4e2c-9099-8cbf58b20f0b).
--
--   [Source excerpt, lines 55–58](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L55-L58) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/EnergyForm.lean#L54-L79 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.EnergyForm`, declaration `FunctionalInequalities.Analysis.CoordinateTensor.contDiffAt_energyForm`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_EnergyForm

variable {n r : ℕ}

theorem FunctionalInequalities.Analysis.CoordinateTensor.contDiffAt_energyForm_readable (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (hA : IsUnit A)
    (T : (Fin r → Fin n) → ℝ) :
    ContDiffAt ℝ 2 (fun q : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × ((Fin r → Fin n) → ℝ) =>
      energyForm q.1 q.2) (A, T) := by sorry
