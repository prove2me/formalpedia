-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_Isotropic_norm_coordTensor_taylorTensor_one_le_of_entries_readable
-- name    : FunctionalInequalities.KLS.Isotropic.norm_coordTensor_taylorTensor_one_le_of_entries_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:19:05.197292+00:00
-- url     : https://prove2.me/theorems/368cfad9-ddaa-46ae-9c1e-acc8bb0d753f
-- title:
--   First Taylor Coordinate Tensor Bound Given Its Entry Formula
-- statement:
--   This is a conditional first-order Taylor tensor norm bound under isotropy.
--
--   Let $n\in\mathbb N$, $E=$ `EuclideanSpace ℝ (Fin n)`, and $(e_j)$ its standard orthonormal basis. Assume:
--
--   1. $\mu$ is an isotropic probability measure (`KLS.Isotropic`), meaning finite second moment, zero mean, and identity covariance.
--   2. $f:E\to\mathbb R$ satisfies `MemLp f 2 μ`.
--   3. The coordinate array $A=$ `Analysis.Tensor.coordTensor` of `Analysis.BakryEmery.taylorTensor μ f 1` satisfies, for every $i:\operatorname{Fin}(1)\to\operatorname{Fin}(n)$,
--   $$
--   A_i=\int\langle e_{i(0)},x\rangle f(x)\,d\mu(x).
--   $$
--   Then its Euclidean coordinate norm satisfies
--   $$
--   \|A\|\le\bigl(\operatorname{eLpNorm}(f,2,\mu)\bigr).\operatorname{toReal}.
--   $$
--   This supplies the first-order tensor estimate when the entry identity is available; it does not establish that identity.
--
--   **Formalization Note** `eLpNorm` takes values in $[0,\infty]$, and the statement explicitly uses its `toReal`. The `MemLp` hypothesis ensures finiteness. No log-concavity, smoothness, or positive-dimension assumption is imposed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem Isotropic.norm_coordTensor_taylorTensor_one_le_of_entries {n : ℕ}
--       {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hiso : Isotropic μ)
--       {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
--       (hentry : ∀ i : Fin 1 → Fin n,
--         coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
--             (taylorTensor (μ : Measure (EuclideanSpace ℝ (Fin n))) f 1) i =
--           ∫ x, ⟪EuclideanSpace.basisFun (Fin n) ℝ (i 0), x⟫ * f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) :
--       ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
--           (taylorTensor (μ : Measure (EuclideanSpace ℝ (Fin n))) f 1)‖ ≤
--         (eLpNorm f 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Reduction`](https://prove2.me/theorems/777aa78c-b385-4e2a-916c-1b5126410eae).
--
--   Definition modules: [`Analysis/Tensor/Coefficients`](https://prove2.me/theorems/88ad50f9-51e6-4e95-905e-5bcdc077739f), [`Analysis/Tensor/Coordinate`](https://prove2.me/theorems/024d1767-7544-4265-9acb-d8fe6f0df92f), [`KLS/Isotropic`](https://prove2.me/theorems/b8da0fa3-d27f-46ae-b3b9-8c204df57e02), [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Supporting theorems: [`integral_sq_eq_affine_decomposition`](https://prove2.me/theorems/77f34311-b8ed-4189-84bc-10fd3772875b).
--
--   Previous: [`coordTensor_taylorTensor_one_apply`](https://prove2.me/theorems/a9935a3a-2011-4a81-95f1-d32208e68e3c) · Next: [`poincare_le_of_cumulantBound`](https://prove2.me/theorems/0b4bd144-4221-4e5f-a91d-90cbadac41af).
--
--   [Source excerpt, lines 49–58](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Reduction.lean#L49-L58) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Reduction.lean#L47-L147 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Reduction`, declaration `FunctionalInequalities.KLS.Isotropic.norm_coordTensor_taylorTensor_one_le_of_entries`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Reduction

open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace

theorem FunctionalInequalities.KLS.Isotropic.norm_coordTensor_taylorTensor_one_le_of_entries_readable {n : ℕ}
    {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hiso : Isotropic μ)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))))
    (hentry : ∀ i : Fin 1 → Fin n,
      coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
          (taylorTensor (μ : Measure (EuclideanSpace ℝ (Fin n))) f 1) i =
        ∫ x, ⟪EuclideanSpace.basisFun (Fin n) ℝ (i 0), x⟫ * f x ∂(μ : Measure (EuclideanSpace ℝ (Fin n)))) :
    ‖coordTensor (EuclideanSpace.basisFun (Fin n) ℝ)
        (taylorTensor (μ : Measure (EuclideanSpace ℝ (Fin n))) f 1)‖ ≤
      (eLpNorm f 2 (μ : Measure (EuclideanSpace ℝ (Fin n)))).toReal := by sorry
