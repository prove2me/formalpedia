-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_Tensor_sum_perm_inner_init_last_readable
-- name    : FunctionalInequalities.Analysis.Tensor.sum_perm_inner_init_last_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:28.19325+00:00
-- url     : https://prove2.me/theorems/21685786-ff33-430e-9d2e-110686ae2c53
-- title:
--   Permutation Sum for a Symmetric Multilinear Map
-- statement:
--   This statement evaluates a permutation sum for a symmetric continuous multilinear map.
--
--   Let $E$ be a real inner-product space, let $d\in\mathbb N$, and let $\Phi:E^d\to E$ be a continuous $d$-linear map satisfying
--
--   $$
--   \Phi(v\circ\tau)=\Phi(v)
--   $$
--
--   for every permutation $\tau$ of $\operatorname{Fin}(d)$ and every $v:\operatorname{Fin}(d)\to E$. For $h:\operatorname{Fin}(d+1)\to E$, one has
--
--   $$
--   \sum_{\sigma\in\operatorname{Sym}(d+1)}
--   \left\langle
--   \Phi\bigl(\operatorname{init}(h\circ\sigma)\bigr),
--    h(\sigma(\operatorname{last}(d)))
--   \right\rangle
--   =(d!)\sum_{k\in\operatorname{Fin}(d+1)}
--   \left\langle
--   \Phi(\operatorname{removeNth}(k,h)),h(k)
--   \right\rangle.
--   $$
--
--   This is the counting identity underlying symmetrization of a multilinear map paired with one additional vector.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.Tensor`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_perm_inner_init_last {d : ℕ} (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) E)
--       (hΦ : ∀ (τ : Equiv.Perm (Fin d)) (v : Fin d → E), Φ (v ∘ τ) = Φ v) (h : Fin (d + 1) → E) :
--       ∑ σ : Equiv.Perm (Fin (d + 1)), ⟪Φ (Fin.init (h ∘ σ)), h (σ (Fin.last d))⟫ =
--         (d.factorial : ℝ) * ∑ k : Fin (d + 1), ⟪Φ (k.removeNth h), h k⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Tensor/Multilinear`](https://prove2.me/theorems/95acd8c3-b570-4032-a49b-c00dac41b021).
--
--   Supporting theorems: [`card_filter_perm_apply_last_eq`](https://prove2.me/theorems/2514fc9f-d962-4adc-9af7-2d50a1e76cfe), [`exists_perm_init_comp_eq`](https://prove2.me/theorems/85188848-2290-4444-9fa3-ed04c8253b48).
--
--   Previous: [`exists_perm_init_comp_eq`](https://prove2.me/theorems/85188848-2290-4444-9fa3-ed04c8253b48).
--
--   [Source excerpt, lines 166–169](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Tensor/Multilinear.lean#L166-L169) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Tensor/Multilinear.lean#L164-L227 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Tensor.Multilinear`, declaration `FunctionalInequalities.Analysis.Tensor.sum_perm_inner_init_last`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Multilinear

open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.Tensor.sum_perm_inner_init_last_readable {d : ℕ} (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) E)
    (hΦ : ∀ (τ : Equiv.Perm (Fin d)) (v : Fin d → E), Φ (v ∘ τ) = Φ v) (h : Fin (d + 1) → E) :
    ∑ σ : Equiv.Perm (Fin (d + 1)), ⟪Φ (Fin.init (h ∘ σ)), h (σ (Fin.last d))⟫ =
      (d.factorial : ℝ) * ∑ k : Fin (d + 1), ⟪Φ (k.removeNth h), h k⟫ := by sorry
