-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_apply_eq_sum_coordTensor_readable
-- name    : FunctionalInequalities.Analysis.Tensor.apply_eq_sum_coordTensor_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:19.923499+00:00
-- url     : https://prove2.me/theorems/8f695d42-8d17-42ff-8947-34303d3bbf9f
-- title:
--   Orthonormal Basis Expansion of a Multilinear Form
-- statement:
--   This is the coordinate expansion of a real continuous multilinear form.
--
--   Let $E$ be a real inner-product space, let $b$ be an orthonormal basis indexed by $\operatorname{Fin}(n)$, let $\Phi:E^k\to\mathbb R$ be a continuous $k$-linear map, and let $h_0,\ldots,h_{k-1}\in E$. Then
--
--   $$\Phi(h_0,\ldots,h_{k-1})
--   =\sum_{i:\operatorname{Fin}(k)\to\operatorname{Fin}(n)}\operatorname{coordTensor}_b(\Phi)(i)\prod_{j=0}^{k-1}\langle b(i_j),h_j\rangle.$$
--
--   The formula expresses a multilinear form through its coordinate tensor in an orthonormal basis.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem apply_eq_sum_coordTensor {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
--       (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) (h : Fin k → E) :
--       Φ h = ∑ i : Fin k → Fin n, coordTensor b Φ i * ∏ j, ⟪b (i j), h j⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/Coefficients`](https://prove2.me/theorems/88ad50f9-51e6-4e95-905e-5bcdc077739f).
--
--   Next: [`norm_coordTensor_le`](https://prove2.me/theorems/fe64a874-0aad-495c-87d8-2d0977852b27).
--
--   [Source excerpt, lines 108–110](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Coefficients.lean#L108-L110) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Coefficients.lean#L107-L125 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Coefficients`, declaration `FunctionalInequalities.Analysis.Tensor.apply_eq_sum_coordTensor`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Coefficients

open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.Tensor.apply_eq_sum_coordTensor_readable {n k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) (h : Fin k → E) :
    Φ h = ∑ i : Fin k → Fin n, coordTensor b Φ i * ∏ j, ⟪b (i j), h j⟫ := by sorry
