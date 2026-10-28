-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_exists_mem_fixingOutside_image_eq_readable
-- name    : FunctionalInequalities.Analysis.Tensor.exists_mem_fixingOutside_image_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:58.869015+00:00
-- url     : https://prove2.me/theorems/14b5df8e-d013-4b01-a20c-a437a2621fc7
-- title:
--   Permutation Matching Equal-Size Subsets Inside a Finite Set
-- statement:
--   This is a finite-combinatorial auxiliary lemma.
--
--   Let $\Omega$ be finite and let $s,t,W\subseteq\Omega$ be finite subsets. Assume $s\subseteq W$, $t\subseteq W$, and $|s|=|t|$. Then there exists a permutation $\sigma$ of $\Omega$ such that $\sigma$ fixes every point outside $W$ and
--
--   $$
--   \sigma(s)=t.
--   $$
--
--   The result supplies the permutation used to compare fibers of the image map on permutations supported inside $W$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_mem_fixingOutside_image_eq {W s t : Finset Ω} (hs : s ⊆ W) (ht : t ⊆ W)
--       (hst : s.card = t.card) : ∃ σ ∈ fixingOutside W, s.image σ = t
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/Symmetrization`](https://prove2.me/theorems/8547f114-355c-49be-8989-b3003d84814f).
--
--   Previous: [`sum_norm_sq_le_sum_norm_sq_sum_subset`](https://prove2.me/theorems/2747bdb8-2573-4a48-9d87-e05edbda390e) · Next: [`apply_eq_of_image_eq`](https://prove2.me/theorems/d208003e-b651-43c5-a3e4-e5c080e8a606).
--
--   [Source excerpt, lines 464–465](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L464-L465) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Symmetrization.lean#L462-L602 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Symmetrization`, declaration `FunctionalInequalities.Analysis.Tensor.exists_mem_fixingOutside_image_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem FunctionalInequalities.Analysis.Tensor.exists_mem_fixingOutside_image_eq_readable {W s t : Finset Ω} (hs : s ⊆ W) (ht : t ⊆ W)
    (hst : s.card = t.card) : ∃ σ ∈ fixingOutside W, s.image σ = t := by sorry
