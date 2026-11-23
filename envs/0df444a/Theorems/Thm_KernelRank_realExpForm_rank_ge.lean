-- Prove2me | Theorems.Thm_KernelRank_realExpForm_rank_ge
-- name    : KernelRank.realExpForm_rank_ge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:20:16.519153+00:00
-- url     : https://prove2.me/theorems/36600c5e-4764-456c-9a95-1ea89802b171
-- title:
--   Kernel Rank: real Exp Form rank ge
-- statement:
--   Alder–Strassen peeling lower bound for `realExpForm` across both real and nonreal rates of
--   arbitrary polynomial degrees.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L1687-L2192
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L1687-L2192

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.realExpForm_rank_ge {ι_R ι_C : Type*} [Fintype ι_R] [Fintype ι_C] {d : ℕ} (hd : 2 ≤ d)
    (m_R : ι_R → ℕ) (m_C : ι_C → ℕ) (c_C : ι_C → ℕ) (hcC : ∀ k, c_C k ≤ m_C k)
    (w_C : ι_C → ℕ → ℂ) (hwC : ∀ k, 0 < c_C k → w_C k (c_C k - 1) ≠ 0) :
    ∀ (S : ℕ) (c_R : ι_R → ℕ), ∑ i, c_R i = S → (∀ i, c_R i ≤ m_R i) →
      ∀ (w_R : ι_R → ℕ → ℝ), (∀ i, 0 < c_R i → w_R i (c_R i - 1) ≠ 0) →
      ∀ (R : ℕ) (ℓ : Fin R → Fin d → (RealExpSpace m_R m_C →ₗ[ℝ] ℝ)),
      (∀ u, realExpForm d m_R m_C c_R c_C w_R w_C u = ∑ n, ∏ j, ℓ n j (u j)) →
      (∑ i, if c_R i = 0 then 0 else (d - 1) * (c_R i - 1) + 1) +
        (∑ k, if c_C k = 0 then 0 else 2 * (d - 1) * (c_C k - 1) + d) ≤ R := by sorry
