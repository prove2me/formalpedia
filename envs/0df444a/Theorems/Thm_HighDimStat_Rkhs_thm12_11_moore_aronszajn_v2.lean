-- Prove2me | Theorems.Thm_HighDimStat_Rkhs_thm12_11_moore_aronszajn_v2
-- name    : HighDimStat.Rkhs.thm12_11_moore_aronszajn_v2
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T03:16:47.46084+00:00
-- url     : https://prove2.me/theorems/2662f35a-1084-4937-8993-f1f129f0068f
-- title:
--   Theorem 12.11 — The Moore-Aronszajn Theorem (Type 0)
-- statement:
--   Given any positive semidefinite kernel function $K : X \times X \to \mathbb{R}$ on a type $X : \mathrm{Type}$, there exists a real Hilbert space $H : \mathrm{Type}$ (embedded into functions on $X$ via $\mathrm{toFun} : H \to_{\mathbb{R}} (X \to \mathbb{R})$) in which the kernel satisfies the reproducing property via a feature map $\mathrm{feature} : X \to H$, and this Hilbert space is unique up to a unique linear isometry equivalence intertwining the function embeddings (repaired universe binder `{X : Type}` matching `H : Type`).

import Mathlib
import Definitions.Def_HighDimStat_Rkhs_Core

namespace HighDimStat.Rkhs

open scoped RealInnerProductSpace

/-- Theorem 12.11 (the Moore-Aronszajn theorem, p. 389): given any positive semidefinite
kernel function `K` on `X : Type`, there is a Hilbert space `H : Type` (embedded into functions
on `X` via `toFun`) in which the kernel satisfies the reproducing property (12.3) via a feature
map `feature`, and this Hilbert space is unique: any two such Hilbert spaces for the same `K` are
linearly isometric via an equivalence that intertwines their embeddings into functions on `X`. -/
theorem thm12_11_moore_aronszajn_v2 {X : Type} (K : X → X → ℝ) (hK : IsPSDKernel K) :
    (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
        (toFun : H →ₗ[ℝ] (X → ℝ)) (feature : X → H), IsRKHS K toFun feature) ∧
      (∀ (H₁ : Type) (_ : NormedAddCommGroup H₁) (_ : InnerProductSpace ℝ H₁)
          (_ : CompleteSpace H₁) (toFun₁ : H₁ →ₗ[ℝ] (X → ℝ)) (feature₁ : X → H₁),
          IsRKHS K toFun₁ feature₁ →
        ∀ (H₂ : Type) (_ : NormedAddCommGroup H₂) (_ : InnerProductSpace ℝ H₂)
          (_ : CompleteSpace H₂) (toFun₂ : H₂ →ₗ[ℝ] (X → ℝ)) (feature₂ : X → H₂),
          IsRKHS K toFun₂ feature₂ →
        ∃ e : H₁ ≃ₗᵢ[ℝ] H₂, ∀ f : H₁, toFun₂ (e f) = toFun₁ f) := by sorry

end HighDimStat.Rkhs
