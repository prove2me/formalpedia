-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_coordTensor_sq_eq_readable
-- name    : FunctionalInequalities.Analysis.Tensor.sum_coordTensor_sq_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:18.956334+00:00
-- url     : https://prove2.me/theorems/43928816-0a65-4412-bbe2-8abe0018771e
-- title:
--   Basis Independence of Coordinate Tensor Square Sums
-- statement:
--   This is the basis-independence identity for the squared coefficient sum of a multilinear form.
--
--   Let $E$ be a real inner-product space, let $b$ and $b'$ be orthonormal bases indexed by $\operatorname{Fin}(n)$ and $\operatorname{Fin}(n')$, respectively, and let $\Phi:E^k\to\mathbb R$ be continuous and $k$-linear. Then
--
--   $$\sum_{i:\operatorname{Fin}(k)\to\operatorname{Fin}(n)}\operatorname{coordTensor}_b(\Phi)(i)^2
--   =\sum_{l:\operatorname{Fin}(k)\to\operatorname{Fin}(n')}\operatorname{coordTensor}_{b'}(\Phi)(l)^2.$$
--
--   Thus the squared coordinate-tensor norm is independent of the chosen orthonormal basis, even when the indexing types are presented with different finite cardinalities.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_coordTensor_sq_eq {n n' k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
--       (b' : OrthonormalBasis (Fin n') ℝ E)
--       (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :
--       ∑ i : Fin k → Fin n, coordTensor b Φ i ^ 2 = ∑ l : Fin k → Fin n', coordTensor b' Φ l ^ 2
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/BasisChange`](https://prove2.me/theorems/89846a1e-d28c-484e-94fe-f976ef7e2382).
--
--   Definition modules: [`Analysis/Tensor/Coefficients`](https://prove2.me/theorems/88ad50f9-51e6-4e95-905e-5bcdc077739f).
--
--   Supporting theorems: [`apply_eq_sum_coordTensor`](https://prove2.me/theorems/8f695d42-8d17-42ff-8947-34303d3bbf9f).
--
--   [Source excerpt, lines 70–73](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/BasisChange.lean#L70-L73) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/BasisChange.lean#L68-L98 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.BasisChange`, declaration `FunctionalInequalities.Analysis.Tensor.sum_coordTensor_sq_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_BasisChange

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.Tensor.sum_coordTensor_sq_eq_readable {n n' k : ℕ} (b : OrthonormalBasis (Fin n) ℝ E)
    (b' : OrthonormalBasis (Fin n') ℝ E)
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :
    ∑ i : Fin k → Fin n, coordTensor b Φ i ^ 2 = ∑ l : Fin k → Fin n', coordTensor b' Φ l ^ 2 := by sorry
