-- Prove2me | Theorems.Thm_KernelRank_exists_rank_le_two_mul_tendstoUniformlyOn_radial_sq_mul_cos
-- name    : KernelRank.exists_rank_le_two_mul_tendstoUniformlyOn_radial_sq_mul_cos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:42:08.136067+00:00
-- url     : https://prove2.me/theorems/9409a9b7-6b06-47eb-ba9b-7e162cb0b59d
-- title:
--   Kernel Rank: exists rank le two mul tendsto Uniformly On radial sq mul cos
-- statement:
--   **Border-rank separation on `‖x‖² cos(‖x‖²)` (`d ≥ 3`).** Specialization of
--   `exists_rank_le_borderTotalCost_tendstoUniformlyOn_radial_profile` to `[⟨I, X⟩]`: on `ℝ^d`
--   (`d ≥ 2`), there exists an explicit family `F h` of real kernels with `separableRank (F h) ≤ 2 d`
--   converging uniformly on every compact subset `C ⊆ ℝ^d` to `‖x‖² cos(‖x‖²)`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Main.lean#L515-L540
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Main.lean#L515-L540

import Definitions.Def_KernelRankLean_Necessity
import Definitions.Def_KernelRankLean_MultiComplexRank
import Definitions.Def_KernelRankLean_MultiRealRank
import Definitions.Def_KernelRankLean_Main
set_option autoImplicit true
open Complex Polynomial Filter Topology
open KernelRank

theorem KernelRank.exists_rank_le_two_mul_tendstoUniformlyOn_radial_sq_mul_cos {d : ℕ} (hd : 2 ≤ d) :
    ∃ F : ℝ → (Fin d → ℝ) → ℝ,
      (∀ h, separableRank (F h) ≤ (2 * d : ℕ)) ∧
      ∀ C : Set (Fin d → ℝ), IsCompact C →
        TendstoUniformlyOn F (fun x => (∑ j, x j ^ 2) * Real.cos (∑ j, x j ^ 2))
          (𝓝[≠] (0 : ℝ)) C := by sorry
