-- Prove2me | Theorems.Thm_HighDimStat_Rkhs_rkhs_uniqueness
-- name    : HighDimStat.Rkhs.rkhs_uniqueness
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-30T14:55:43.021607+00:00
-- url     : https://prove2.me/theorems/35d26be8-d877-4cdf-a3fe-7667796f67aa
-- title:
--   Uniqueness of the reproducing kernel Hilbert space for a PSD kernel
-- statement:
--   Decomposition of HighDimStat.Rkhs.thm12_11_moore_aronszajn (Wainwright, Theorem 12.11), step 3 (uniqueness). Any two Hilbert spaces H₁, H₂ of functions on X with the reproducing property for the same PSD kernel K — injective linear embeddings into X → ℝ with feature maps x ↦ K(·,x) satisfying <u, feature x> = (toFun u) x — coincide: there is a linear isometric equivalence e : H₁ ≃ H₂ with toFun₂ ∘ e = toFun₁. Proof sketch: the feature spans are dense (orthogonal complement trivial by reproducing + injectivity) and x ↦ feature₂ x extends the Gram-preserving map feature₁ x ↦ feature₂ x to a surjective linear isometry.
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

/-- Step 3 of the Moore-Aronszajn construction: uniqueness. Any two Hilbert
    spaces of functions on `X` with the reproducing property for the same
    kernel `K` (injective linear embeddings `toFun₁`, `toFun₂` into `X → ℝ`
    with feature maps satisfying the reproducing identity) are linearly
    isometric via an equivalence intertwining the embeddings. -/
theorem rkhs_uniqueness {X : Type} (K : X → X → ℝ)
    (H₁ H₂ : Type)
    [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
    (toFun₁ : H₁ → X → ℝ) (toFun₂ : H₂ → X → ℝ)
    (hlin₁ : ∀ (u v : H₁) (a b : ℝ),
      toFun₁ (a • u + b • v) = fun x => a * toFun₁ u x + b * toFun₁ v x)
    (hinj₁ : Function.Injective toFun₁)
    (feature₁ : X → H₁)
    (hmem₁ : ∀ x : X, toFun₁ (feature₁ x) = fun y => K y x)
    (hrepr₁ : ∀ (u : H₁) (x : X), inner ℝ u (feature₁ x) = toFun₁ u x)
    (hlin₂ : ∀ (u v : H₂) (a b : ℝ),
      toFun₂ (a • u + b • v) = fun x => a * toFun₂ u x + b * toFun₂ v x)
    (hinj₂ : Function.Injective toFun₂)
    (feature₂ : X → H₂)
    (hmem₂ : ∀ x : X, toFun₂ (feature₂ x) = fun y => K y x)
    (hrepr₂ : ∀ (u : H₂) (x : X), inner ℝ u (feature₂ x) = toFun₂ u x) :
    ∃ e : H₁ ≃ₗ[ℝ] H₂, ∀ u : H₁, toFun₂ (e u) = toFun₁ u := by
  sorry

end HighDimStat.Rkhs
