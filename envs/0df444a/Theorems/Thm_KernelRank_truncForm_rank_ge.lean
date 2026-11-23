-- Prove2me | Theorems.Thm_KernelRank_truncForm_rank_ge
-- name    : KernelRank.truncForm_rank_ge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:14:20.895266+00:00
-- url     : https://prove2.me/theorems/cb6f7451-85aa-4223-9f4f-bf0961dda55c
-- title:
--   Kernel Rank: trunc Form rank ge
-- statement:
--   Alder–Strassen peeling lower bound for `truncForm`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L378-L821
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L378-L821

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.truncForm_rank_ge {ι : Type*} [Fintype ι] {d : ℕ} (hd : 2 ≤ d)
    (m₀ : ι → ℕ) :
    ∀ (S : ℕ) (c : ι → ℕ), ∑ i, c i = S → (∀ i, c i ≤ m₀ i) →
      ∀ (w : ι → ℕ → ℂ), (∀ i, 0 < c i → w i (c i - 1) ≠ 0) →
      ∀ (R : ℕ) (ℓ : Fin R → Fin d → ((∀ i, Fin (m₀ i) → ℂ) →ₗ[ℂ] ℂ)),
      (∀ u, truncForm d m₀ c w u = ∑ n, ∏ j, ℓ n j (u j)) →
      (∑ i, if c i = 0 then 0 else (d - 1) * (c i - 1) + 1) ≤ R := by sorry
