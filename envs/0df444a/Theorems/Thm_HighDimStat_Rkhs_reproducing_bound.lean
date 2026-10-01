-- Prove2me | Theorems.Thm_HighDimStat_Rkhs_reproducing_bound
-- name    : HighDimStat.Rkhs.reproducing_bound
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-30T14:39:53.547594+00:00
-- url     : https://prove2.me/theorems/54a56a6b-4b2f-4761-9f85-de89c48c83f2
-- title:
--   Pointwise evaluation bound on the span of kernel sections (Cauchy-Schwarz)
-- statement:
--   Decomposition of HighDimStat.Rkhs.thm12_11_moore_aronszajn (Wainwright, Theorem 12.11), step 2. Pointwise evaluation bound on the span of kernel sections: for f = ∑ᵢ cᵢK(·,xᵢ), |f z| ≤ √(K z z) · √(Gram sum), the Cauchy-Schwarz corollary of the pre-inner product. Hence point evaluation z ↦ f z is continuous for the pre-inner-product norm, so it extends to the completion — the reproducing property (12.3) of Theorem 12.11.
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

/-- Step 2 of the Moore-Aronszajn construction: the pointwise evaluation bound on
    the span of kernel sections. For `f` a finite linear combination of the
    kernel sections `K · (x i)` one has `|f z| ≤ sqrt (K z z) * sqrt (Gram sum)`,
    the Cauchy-Schwarz corollary that
    makes point evaluation continuous for the pre-inner-product norm. -/
theorem reproducing_bound {X : Type} (K : X → X → ℝ) (hK : IsPSDKernel K) :
    ∀ (n : ℕ) (x : Fin n → X) (c : Fin n → ℝ) (z : X),
      abs (Finset.sum Finset.univ (fun i => c i * K z (x i))) ≤
        Real.sqrt (K z z) *
          Real.sqrt (Finset.sum Finset.univ (fun i =>
            Finset.sum Finset.univ (fun j => c i * c j * K (x i) (x j)))) := by
  sorry

end HighDimStat.Rkhs
