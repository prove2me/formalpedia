-- Prove2me | Theorems.Thm_KernelRank_exp_smul_apply_of_genEigen
-- name    : KernelRank.exp_smul_apply_of_genEigen
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:12:12.895802+00:00
-- url     : https://prove2.me/theorems/95fe5f1f-eb56-47d8-94b1-0ec5e6da206d
-- title:
--   Kernel Rank: exp smul apply of gen Eigen
-- statement:
--   On a generalized eigenvector with eigenvalue `μ`, `exp (t A)` acts as `exp (μ t)` times a
--   polynomial in `t`.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Necessity.lean#L33-L72
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Necessity.lean#L33-L72

import Definitions.Def_KernelRankLean_TranslationSemigroup
import Definitions.Def_KernelRankLean_Representation
import Definitions.Def_KernelRankLean_Necessity
set_option autoImplicit true
open Complex Polynomial NNReal
open KernelRank
attribute [local instance] translateNormedAddCommGroup translateNormedSpace
  translateUniformSpace translateCompleteSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem KernelRank.exp_smul_apply_of_genEigen (A : E →L[ℂ] E) (μ : ℂ) {v : E} {k : ℕ}
    (hv : ((A.toLinearMap - μ • 1) ^ k) v = 0) (t : ℂ) :
    NormedSpace.exp (t • A) v = ∑ m ∈ Finset.range k,
      (Complex.exp (μ * t) * ((m.factorial : ℂ)⁻¹ * t ^ m)) • ((A - μ • 1) ^ m) v := by sorry
