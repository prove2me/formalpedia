-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_coordTensor_taylorTensor_one_apply_readable
-- name    : FunctionalInequalities.KLS.coordTensor_taylorTensor_one_apply_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:19:43.977657+00:00
-- url     : https://prove2.me/theorems/a9935a3a-2011-4a81-95f1-d32208e68e3c
-- title:
--   First Taylor Tensor Coordinate Formula
-- statement:
--   This statement identifies each coordinate of the first Taylor tensor for a centered probability measure.
--
--   Let $n\in\mathbb N$ and let $\mu$ be a probability measure on $\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin} n)$. Assume:
--
--   1. For every $r\in\mathbb R$, the function $x\mapsto\exp(r\|x\|)$ is integrable with respect to $\mu$.
--   2. The identity map belongs to $L^2(\mu)$.
--   3. The mean of $\mu$ is zero, namely $\int x\,d\mu=0$.
--   4. The function $f:\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin} n)\to\mathbb R$ belongs to $L^2(\mu)$.
--
--   Then, for every index map $i:\operatorname{Fin}1\to\operatorname{Fin}n$,
--
--   $$
--   \operatorname{coordTensor}(e,\operatorname{taylorTensor}(\mu,f,1))(i)
--   =\int \left\langle e_{i(0)},x\right\rangle f(x)\,d\mu(x),
--   $$
--
--   where $e$ is the standard basis.
--
--   This is the degree-one coordinate identity used to control the linear Taylor component in the Poincaré reduction.
--
--   **Formalization Note**: The integral and the coordinate tensor are those of `coordTensor` and `taylorTensor`; the hypotheses explicitly provide exponential integrability, second-moment integrability, centering, and square integrability.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem coordTensor_taylorTensor_one_apply {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
--       [IsProbabilityMeasure μ] (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
--       (hμ2 : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 μ)
--       (hμ0 : ∫ x, x ∂μ = 0) {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ)
--       (i : Fin 1 → Fin n) :
--       coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ f 1) i =
--         ∫ x, ⟪EuclideanSpace.basisFun (Fin n) ℝ (i 0), x⟫ * f x ∂μ
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Reduction`](https://prove2.me/theorems/777aa78c-b385-4e2a-916c-1b5126410eae).
--
--   Definition modules: [`Analysis/Tensor/Coefficients`](https://prove2.me/theorems/88ad50f9-51e6-4e95-905e-5bcdc077739f), [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a).
--
--   Supporting theorems: [`taylorTensor_one_apply`](https://prove2.me/theorems/5f1e7c9b-800d-4d4b-84f5-1fa20ecda112).
--
--   Next: [`Isotropic.norm_coordTensor_taylorTensor_one_le_of_entries`](https://prove2.me/theorems/368cfad9-ddaa-46ae-9c1e-acc8bb0d753f).
--
--   [Source excerpt, lines 24–30](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Reduction.lean#L24-L30) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Reduction.lean#L23-L45 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Reduction`, declaration `FunctionalInequalities.KLS.coordTensor_taylorTensor_one_apply`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Reduction

open MeasureTheory FunctionalInequalities.Analysis.BakryEmery FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace

theorem FunctionalInequalities.KLS.coordTensor_taylorTensor_one_apply_readable {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    (hμ2 : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2 μ)
    (hμ0 : ∫ x, x ∂μ = 0) {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : MemLp f 2 μ)
    (i : Fin 1 → Fin n) :
    coordTensor (EuclideanSpace.basisFun (Fin n) ℝ) (taylorTensor μ f 1) i =
      ∫ x, ⟪EuclideanSpace.basisFun (Fin n) ℝ (i 0), x⟫ * f x ∂μ := by sorry
