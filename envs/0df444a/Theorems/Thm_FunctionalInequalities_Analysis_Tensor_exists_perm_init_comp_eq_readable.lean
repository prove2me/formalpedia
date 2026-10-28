-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_exists_perm_init_comp_eq_readable
-- name    : FunctionalInequalities.Analysis.Tensor.exists_perm_init_comp_eq_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:30.649316+00:00
-- url     : https://prove2.me/theorems/85188848-2290-4444-9fa3-ed04c8253b48
-- title:
--   Permutation of Entries After Removing One Index
-- statement:
--   This statement describes the first $d$ entries of a permuted $(d+1)$-tuple.
--
--   Let $\alpha$ be a type, let $h:\operatorname{Fin}(d+1)\to\alpha$, let $\sigma$ be a permutation of $\operatorname{Fin}(d+1)$, and let $k\in\operatorname{Fin}(d+1)$. If
--
--   $$
--   \sigma(\operatorname{last}(d))=k,
--   $$
--
--   then there exists a permutation $\tau$ of $\operatorname{Fin}(d)$ such that
--
--   $$
--   \operatorname{init}(h\circ\sigma)=\operatorname{removeNth}(k,h)\circ\tau.
--   $$
--
--   Thus, after the entry indexed by $k$ is removed, the remaining entries agree up to permutation. This technical lemma supports reorganizing symmetrized multilinear expressions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_perm_init_comp_eq {α : Type*} {d : ℕ} (h : Fin (d + 1) → α)
--       (σ : Equiv.Perm (Fin (d + 1))) {k : Fin (d + 1)} (hk : σ (Fin.last d) = k) :
--       ∃ τ : Equiv.Perm (Fin d), Fin.init (h ∘ σ) = k.removeNth h ∘ τ
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/Multilinear`](https://prove2.me/theorems/95acd8c3-b570-4032-a49b-c00dac41b021).
--
--   Previous: [`card_filter_perm_apply_last_eq`](https://prove2.me/theorems/2514fc9f-d962-4adc-9af7-2d50a1e76cfe) · Next: [`sum_perm_inner_init_last`](https://prove2.me/theorems/21685786-ff33-430e-9d2e-110686ae2c53).
--
--   [Source excerpt, lines 135–137](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Multilinear.lean#L135-L137) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Multilinear.lean#L134-L162 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Multilinear`, declaration `FunctionalInequalities.Analysis.Tensor.exists_perm_init_comp_eq`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Multilinear

theorem FunctionalInequalities.Analysis.Tensor.exists_perm_init_comp_eq_readable {α : Type*} {d : ℕ} (h : Fin (d + 1) → α)
    (σ : Equiv.Perm (Fin (d + 1))) {k : Fin (d + 1)} (hk : σ (Fin.last d) = k) :
    ∃ τ : Equiv.Perm (Fin d), Fin.init (h ∘ σ) = k.removeNth h ∘ τ := by sorry
