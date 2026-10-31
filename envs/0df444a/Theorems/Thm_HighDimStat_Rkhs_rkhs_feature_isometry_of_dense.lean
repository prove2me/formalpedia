-- Prove2me | Theorems.Thm_HighDimStat_Rkhs_rkhs_feature_isometry_of_dense
-- name    : HighDimStat.Rkhs.rkhs_feature_isometry_of_dense
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-31T01:50:09.655198+00:00
-- url     : https://prove2.me/theorems/2ba9f82a-0668-4c89-b668-8441411b19b8
-- title:
--   Feature-preserving linear isometry between two RKHSs of the same PSD kernel
-- statement:
--   Given two reproducing kernel Hilbert spaces $(H_1, \mathrm{toFun}_1, \Phi_1)$ and $(H_2, \mathrm{toFun}_2, \Phi_2)$ for the same positive semidefinite kernel $K$ whose feature spans have trivial orthogonal complements and whose feature vectors have identical Gram inner products $\langle \Phi_1(x), \Phi_1(y) \rangle_{H_1} = \langle \Phi_2(x), \Phi_2(y) \rangle_{H_2}$, there exists a linear isometry equivalence $e : H_1 \simeq_{\ell i} H_2$ sending $\Phi_1(x)$ to $\Phi_2(x)$ for all $x \in X$.

import Mathlib
import Definitions.Def_HighDimStat_Rkhs_Core

namespace HighDimStat.Rkhs

open scoped RealInnerProductSpace

/-- **Feature-preserving linear isometry between two RKHSs of the same PSD kernel (Wainwright Theorem 12.11, p. 389).**
Given two RKHSs `(H₁, toFun₁, feature₁)` and `(H₂, toFun₂, feature₂)` for the same positive
semidefinite kernel `K` whose feature spans have trivial orthogonal complements and whose feature
inner products satisfy `⟪feature₁ x, feature₁ y⟫ = ⟪feature₂ x, feature₂ y⟫`, there exists
a linear isometry equivalence `e : H₁ ≃ₗᵢ[ℝ] H₂` sending `feature₁ x` to `feature₂ x` for all `x`. -/
theorem rkhs_feature_isometry_of_dense {X : Type*} (K : X → X → ℝ) (hK : IsPSDKernel K)
    (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
    (toFun₁ : H₁ →ₗ[ℝ] (X → ℝ)) (feature₁ : X → H₁) (h₁ : IsRKHS K toFun₁ feature₁)
    (h_orth₁ : (Submodule.span ℝ (Set.range feature₁))ᗮ = ⊥)
    (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]
    (toFun₂ : H₂ →ₗ[ℝ] (X → ℝ)) (feature₂ : X → H₂) (h₂ : IsRKHS K toFun₂ feature₂)
    (h_orth₂ : (Submodule.span ℝ (Set.range feature₂))ᗮ = ⊥)
    (h_gram : ∀ x y : X, ⟪feature₁ x, feature₁ y⟫ = ⟪feature₂ x, feature₂ y⟫) :
    ∃ e : H₁ ≃ₗᵢ[ℝ] H₂, ∀ x : X, e (feature₁ x) = feature₂ x := by sorry

end HighDimStat.Rkhs
