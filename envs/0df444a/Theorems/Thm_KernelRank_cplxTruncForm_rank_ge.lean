-- Prove2me | Theorems.Thm_KernelRank_cplxTruncForm_rank_ge
-- name    : KernelRank.cplxTruncForm_rank_ge
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:20:12.03173+00:00
-- url     : https://prove2.me/theorems/063a7ab4-2f60-4fdf-abab-f8838e27c788
-- title:
--   Kernel Rank: cplx Trunc Form rank ge
-- statement:
--   Alder–Strassen peeling lower bound for `cplxTruncForm` (`2 * (d - 1) * (c k - 1) + d` per
--   active nonreal rate).
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L1024-L1683
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiRealRank.lean#L1024-L1683

import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_RealExpPoly
import Definitions.Def_KernelRankLean_MultiRealRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.cplxTruncForm_rank_ge {ι_C : Type*} [Fintype ι_C] {d : ℕ} (hd : 2 ≤ d)
    (m_C : ι_C → ℕ) :
    ∀ (S : ℕ) (c : ι_C → ℕ), ∑ k, c k = S → (∀ k, c k ≤ m_C k) →
      ∀ (w : ι_C → ℕ → ℂ), (∀ k, 0 < c k → w k (c k - 1) ≠ 0) →
      ∀ (R : ℕ) (ℓ : Fin R → Fin d → (CplxExpSpace m_C →ₗ[ℝ] ℝ)),
      (∀ u, cplxTruncForm d m_C c w u = ∑ n, ∏ j, ℓ n j (u j)) →
      (∑ k, if c k = 0 then 0 else 2 * (d - 1) * (c k - 1) + d) ≤ R := by sorry
