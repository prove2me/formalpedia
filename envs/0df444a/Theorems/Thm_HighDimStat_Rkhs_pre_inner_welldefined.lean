-- Prove2me | Theorems.Thm_HighDimStat_Rkhs_pre_inner_welldefined
-- name    : HighDimStat.Rkhs.pre_inner_welldefined
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-30T14:39:52.163817+00:00
-- url     : https://prove2.me/theorems/151a740b-0f4d-4eb2-a7bf-7ad082d892c8
-- title:
--   Well-definedness of the pre-inner product on the span of kernel sections
-- statement:
--   Decomposition of HighDimStat.Rkhs.thm12_11_moore_aronszajn (Wainwright, Theorem 12.11), step 1. For a positive semidefinite kernel K on X, the bilinear form on the linear span of the kernel sections K(·,x), defined on finite linear combinations by <∑ᵢ cᵢK_{xᵢ}, ∑ⱼ dⱼK_{yⱼ}> = ∑ᵢⱼ cᵢdⱼK(xᵢ,yⱼ), is well-defined: if ∑ᵢ cᵢK(·,xᵢ) vanishes identically then its Gram sum is zero, so the value does not depend on the chosen representation. The form is positive semidefinite by the PSD hypothesis on K. This is the pre-inner product whose completion is the RKHS of Theorem 12.11.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 389 (PDF p. 409), Theorem 12.11, Eq. (12.3)

import Mathlib

namespace HighDimStat.Rkhs

/-- A kernel `K` on `X` is positive semidefinite: every finite Gram matrix is PSD. -/
def IsPSDKernel {X : Type} (K : X → X → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → X) (c : Fin n → ℝ),
    0 ≤ Finset.sum Finset.univ (fun i =>
      Finset.sum Finset.univ (fun j => c i * c j * K (x i) (x j)))

end HighDimStat.Rkhs

namespace HighDimStat.Rkhs

/-- Step 1 of the Moore-Aronszajn construction: for a PSD kernel the Gram sum
    vanishes on every vanishing finite linear combination of kernel sections
    (so the pre-inner product on the span is representation-independent), and
    the Gram sum is nonnegative by the PSD hypothesis. -/
theorem pre_inner_welldefined {X : Type} (K : X → X → ℝ) (hK : IsPSDKernel K) :
    (∀ (n : ℕ) (x : Fin n → X) (c : Fin n → ℝ),
      (∀ z : X, Finset.sum Finset.univ (fun i => c i * K z (x i)) = 0) →
      Finset.sum Finset.univ (fun i =>
        Finset.sum Finset.univ (fun j => c i * c j * K (x i) (x j))) = 0) ∧
    (∀ (n : ℕ) (x : Fin n → X) (c : Fin n → ℝ),
      0 ≤ Finset.sum Finset.univ (fun i =>
        Finset.sum Finset.univ (fun j => c i * c j * K (x i) (x j)))) := by
  sorry

end HighDimStat.Rkhs
