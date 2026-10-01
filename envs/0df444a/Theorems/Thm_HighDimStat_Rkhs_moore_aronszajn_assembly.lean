-- Prove2me | Theorems.Thm_HighDimStat_Rkhs_moore_aronszajn_assembly
-- name    : HighDimStat.Rkhs.moore_aronszajn_assembly
-- status  : Open
-- author  : @junyihjy
-- created : 2026-09-30T15:07:48.591522+00:00
-- url     : https://prove2.me/theorems/f063c309-6884-43aa-afee-05ba4b40e4e4
-- title:
--   Moore-Aronszajn assembly: existence and uniqueness of the RKHS
-- statement:
--   Assembly for HighDimStat.Rkhs.thm12_11_moore_aronszajn (Wainwright, Theorem 12.11). Combines the three decomposition children — HighDimStat.Rkhs.pre_inner_welldefined (the pre-inner product on the span of kernel sections is well-defined and positive semidefinite), HighDimStat.Rkhs.reproducing_bound (point evaluation is continuous for the pre-inner-product norm, so it extends to the completion and gives the reproducing property), and HighDimStat.Rkhs.rkhs_uniqueness (any two such Hilbert spaces are linearly isometric via an equivalence intertwining the embeddings) — into the existence and uniqueness of the reproducing kernel Hilbert space of Theorem 12.11.
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

/-- Assembly for the Moore-Aronszajn theorem: the three decomposition children
    give existence and uniqueness of the RKHS. Existence: the pre-inner product
    on the span of kernel sections (child a, well-defined and PSD) completes to
    a Hilbert space, and point evaluation is continuous (child b), yielding the
    reproducing property. Uniqueness: child (c). -/
theorem moore_aronszajn_assembly {X : Type} (K : X → X → ℝ) (hK : IsPSDKernel K) :
    (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
        (_ : CompleteSpace H) (toFun : H → X → ℝ),
      Function.Injective toFun ∧
      (∀ (u v : H) (a b : ℝ),
        toFun (a • u + b • v) = fun x => a * toFun u x + b * toFun v x) ∧
      ∃ feature : X → H, (∀ x : X, toFun (feature x) = fun y => K y x) ∧
        ∀ (u : H) (x : X), inner ℝ u (feature x) = toFun u x) ∧
    (∀ (H₁ H₂ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
        [CompleteSpace H₁] [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂]
        [CompleteSpace H₂] (toFun₁ : H₁ → X → ℝ) (toFun₂ : H₂ → X → ℝ)
        (hlin₁ : ∀ (u v : H₁) (a b : ℝ),
          toFun₁ (a • u + b • v) = fun x => a * toFun₁ u x + b * toFun₁ v x)
        (hinj₁ : Function.Injective toFun₁) (feature₁ : X → H₁)
        (hmem₁ : ∀ x : X, toFun₁ (feature₁ x) = fun y => K y x)
        (hrepr₁ : ∀ (u : H₁) (x : X), inner ℝ u (feature₁ x) = toFun₁ u x)
        (hlin₂ : ∀ (u v : H₂) (a b : ℝ),
          toFun₂ (a • u + b • v) = fun x => a * toFun₂ u x + b * toFun₂ v x)
        (hinj₂ : Function.Injective toFun₂) (feature₂ : X → H₂)
        (hmem₂ : ∀ x : X, toFun₂ (feature₂ x) = fun y => K y x)
        (hrepr₂ : ∀ (u : H₂) (x : X), inner ℝ u (feature₂ x) = toFun₂ u x),
      ∃ e : H₁ ≃ₗ[ℝ] H₂, ∀ u : H₁, toFun₂ (e u) = toFun₁ u) := by
  sorry

end HighDimStat.Rkhs
