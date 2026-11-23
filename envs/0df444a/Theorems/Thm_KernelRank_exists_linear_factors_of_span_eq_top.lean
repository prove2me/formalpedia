-- Prove2me | Theorems.Thm_KernelRank_exists_linear_factors_of_span_eq_top
-- name    : KernelRank.exists_linear_factors_of_span_eq_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:09:18.367497+00:00
-- url     : https://prove2.me/theorems/67b31765-6cc9-400a-8a0b-a8ea33ed2da5
-- title:
--   Kernel Rank: exists linear factors of span eq top
-- statement:
--   If `v : α → V` spans `V`, any `R`-term coordinatewise product decomposition of
--   `s ↦ T (fun j => v (s j))` induces an `R`-term linear-functional decomposition of `T`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L296-L317
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean#L296-L317

import Definitions.Def_KernelRankLean_ComplexRank
import Definitions.Def_KernelRankLean_MultiComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank

theorem KernelRank.exists_linear_factors_of_span_eq_top {𝕜 α V : Type*} [Field 𝕜] [AddCommGroup V]
    [Module 𝕜 V] {d R : ℕ} {v : α → V} (hv : Submodule.span 𝕜 (Set.range v) = ⊤)
    (T : MultilinearMap 𝕜 (fun _ : Fin d => V) 𝕜)
    (hK : IsSumOfProducts (fun s : Fin d → α => T fun j => v (s j)) R) :
    ∃ ℓ : Fin R → Fin d → (V →ₗ[𝕜] 𝕜),
      ∀ u : Fin d → V, T u = ∑ n, ∏ j, ℓ n j (u j) := by sorry
