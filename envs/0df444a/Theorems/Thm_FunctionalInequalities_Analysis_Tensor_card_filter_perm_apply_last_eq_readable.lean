-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_card_filter_perm_apply_last_eq_readable
-- name    : FunctionalInequalities.Analysis.Tensor.card_filter_perm_apply_last_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:30.47996+00:00
-- url     : https://prove2.me/theorems/2514fc9f-d962-4adc-9af7-2d50a1e76cfe
-- title:
--   Permutation Fiber Cardinality
-- statement:
--   This statement counts permutations with a prescribed image of the last index.
--
--   For $d\in\mathbb N$ and $k\in\operatorname{Fin}(d+1)$, consider permutations $\sigma$ of $\operatorname{Fin}(d+1)$ satisfying $\sigma(\operatorname{last}(d))=k$. Their number is exactly $d!$:
--
--   $$
--   \#\{\sigma\in\operatorname{Sym}(\operatorname{Fin}(d+1)):\sigma(\operatorname{last}(d))=k\}=d!.
--   $$
--
--   This is a finite combinatorial identity used to group permutation sums according to the value of their last argument.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem card_filter_perm_apply_last_eq {d : ℕ} (k : Fin (d + 1)) :
--       (Finset.univ.filter fun σ : Equiv.Perm (Fin (d + 1)) => σ (Fin.last d) = k).card =
--         d.factorial
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/Multilinear`](https://prove2.me/theorems/95acd8c3-b570-4032-a49b-c00dac41b021).
--
--   Next: [`exists_perm_init_comp_eq`](https://prove2.me/theorems/85188848-2290-4444-9fa3-ed04c8253b48).
--
--   [Source excerpt, lines 85–87](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Multilinear.lean#L85-L87) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Multilinear.lean#L84-L132 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Multilinear`, declaration `FunctionalInequalities.Analysis.Tensor.card_filter_perm_apply_last_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Multilinear

theorem FunctionalInequalities.Analysis.Tensor.card_filter_perm_apply_last_eq_readable {d : ℕ} (k : Fin (d + 1)) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin (d + 1)) => σ (Fin.last d) = k).card =
      d.factorial := by sorry
