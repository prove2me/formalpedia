-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_norm_sq_sum_filter_readable
-- name    : FunctionalInequalities.Analysis.Tensor.sum_norm_sq_sum_filter_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:02.464517+00:00
-- url     : https://prove2.me/theorems/f152e5e8-eec5-438e-bbf0-9dca6ce16fe8
-- title:
--   Squared Norm Expansion for Filtered Finite Sums
-- statement:
--   This is a finite-dimensional inner-product expansion.
--
--   Let $V$ be a real inner-product space, let $\mathcal E$ and $P$ be finite sets, let $r(F,E)$ be a decidable relation between $F\in P$ and $E\in\mathcal E$, and let $x_F\in V$. Then
--
--   $$
--   \sum_{E\in\mathcal E}\left\|\sum_{\substack{F\in P\\r(F,E)}}x_F\right\|^2
--   =
--   \sum_{F,F'\in P}
--   \#\{E\in\mathcal E:r(F,E)\land r(F',E)
--   \}\,\langle x_F,x_{F'}\rangle.
--   $$
--
--   This identity is a reusable way to expand sums of squared norms while retaining the multiplicity of common filters.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_norm_sq_sum_filter {β ι : Type*} (𝓔 : Finset β) (P : Finset ι) (r : ι → β → Prop)
--       [∀ F E, Decidable (r F E)] (x : ι → V) :
--       ∑ E ∈ 𝓔, ‖∑ F ∈ P.filter (fun F => r F E), x F‖ ^ 2 =
--         ∑ F ∈ P, ∑ F' ∈ P, ((𝓔.filter fun E => r F E ∧ r F' E).card : ℝ) * inner ℝ (x F) (x F')
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/Symmetrization`](https://prove2.me/theorems/8547f114-355c-49be-8989-b3003d84814f).
--
--   Previous: [`sum_choose_mul_card_filter_subset`](https://prove2.me/theorems/bdbd40ac-1a0c-4040-b7c6-4891fcad5583) · Next: [`sum_norm_sq_sum_subset_eq`](https://prove2.me/theorems/3f94b763-454c-46a7-862d-4d84329a2ef7).
--
--   [Source excerpt, lines 222–225](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L222-L225) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L220-L259 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.sum_norm_sq_sum_filter`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem FunctionalInequalities.Analysis.Tensor.sum_norm_sq_sum_filter_readable {β ι : Type*} (𝓔 : Finset β) (P : Finset ι) (r : ι → β → Prop)
    [∀ F E, Decidable (r F E)] (x : ι → V) :
    ∑ E ∈ 𝓔, ‖∑ F ∈ P.filter (fun F => r F E), x F‖ ^ 2 =
      ∑ F ∈ P, ∑ F' ∈ P, ((𝓔.filter fun E => r F E ∧ r F' E).card : ℝ) * inner ℝ (x F) (x F') := by sorry
