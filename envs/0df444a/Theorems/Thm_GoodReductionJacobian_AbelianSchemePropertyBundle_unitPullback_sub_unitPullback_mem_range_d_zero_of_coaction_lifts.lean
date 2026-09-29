-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_unitPullback_sub_unitPullback_mem_range_d_zero_of_coaction_lifts
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.unitPullback_sub_unitPullback_mem_range_d_zero_of_coaction_lifts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/0161181b-9c56-521b-a554-a5c79f14627d
-- title:
--   Pull-back of descended difference cochains modulo coboundaries
-- statement:
--   Let $K$ be a field, $A$ a scheme and $f : A \to \operatorname{Spec} K$ a morphism satisfying `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, every fibre of the underlying map is connected, and $f$ admits a relative group law; let $N : A \to A$ satisfy $N$ followed by $f$ equals $f$, and let $H$ be a commutative $K$-algebra. Each $\Gamma(A,V)$ is regarded as a $K$-algebra through $f$. Assume given, for every affine open $U$, a $K$-algebra map $\rho_U : \Gamma(A, N^{-1}U) \to \Gamma(A,N^{-1}U) \otimes_K H$, compatible with restriction along inclusions $N^{-1}U' \subseteq N^{-1}U$ via $\mathrm{id}_H$ (`hnat`), such that $N^{\sharp}$ on $U$ is injective (`hinj`) and every $s$ with $\rho_U(s) = s \otimes 1$ lies in the image of $N^{\sharp}$ (`hcoinv`). Assume further $\varphi : A \to A$ with $\varphi$ followed by $N$ equal to $N$ followed by $\varphi$, and a $K$-algebra map $\varphi_H : H \to H$, such that for affine opens $U, W$ with $N^{-1}W \subseteq \varphi^{-1}N^{-1}U$ there is a ring homomorphism $\Xi$ on the tensor products with $\Xi(s \otimes 1) = \varphi^{\sharp}s \otimes 1$, $\Xi(1 \otimes x) = 1 \otimes \varphi_H x$ and $\Xi \circ \rho_U = \rho_W \circ \varphi^{\sharp}$. Let $\mathcal K, \mathcal W$ be ordered affine covers of $A$ (finite linearly ordered index sets, affine opens with total supremum $\top$), and $\lambda, \lambda' : \mathcal W_\iota \to \mathcal K_\iota$ with $\mathcal W_w \subseteq \varphi^{-1}\mathcal K_{\lambda w}$ and $\mathcal W_w \subseteq \mathrm{id}^{-1}\mathcal K_{\lambda' w}$. Let $h, h' \in H$ with $\varphi_H h = h'$, and let $S_i, S'_i \in \Gamma(A, N^{-1}\mathcal K_i)$ satisfy $\rho(S_i) = S_i \otimes 1 + 1 \otimes h$ and $\rho(S'_i) = S'_i \otimes 1 + 1 \otimes h'$. Finally let $c, c'$ be degree-one Čech cochains of the presheaf `OModulePresheaf.unit f` (so $c_t \in \Gamma(A, \mathcal K_{t_0} \cap \mathcal K_{t_1})$ for strictly monotone pairs $t$) with $N^{\sharp}c_t$ equal to the difference of the restrictions of $S_{t_0}$ and $S_{t_1}$, and likewise for $c'$ and $S'$. Then the signed refinement pull-back of $c$ along $\varphi$ and $\lambda$ minus that of $c'$ along $\mathrm{id}_A$ and $\lambda'$ lies in the range of the degree-zero Čech differential of `OModulePresheaf.unit f` on $\mathcal W$.
--
--   This is the functoriality (equivariance) step for the degree-one Čech class attached to a chartwise lift of an element of $H$ along the coaction $\rho$: the class of the descended difference cocycle is unchanged, up to coboundaries on a refining cover, when one pulls back along a morphism $\varphi$ commuting with $N$ and matching $h$ with $h' = \varphi_H h$. It feeds the construction of a linear map on primitives out of cocycles in the characteristic-$p$ setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_unitPullback_sub_unitPullback_mem_range_d_zero_of_coaction_lifts.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.unitPullback_sub_unitPullback_mem_range_d_zero_of_coaction_lifts
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (N : A ⟶ A) (hN : N ≫ f = f)
    (H : Type u) [CommRing H] [Algebra K H] :
    letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
    ∀ (ρ : ∀ U : A.affineOpens, Γ(A, N ⁻¹ᵁ (U : A.Opens)) →ₐ[K] Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H)
      (hnat : ∀ (U U' : A.affineOpens) (hle : (N ⁻¹ᵁ (U' : A.Opens)) ≤ N ⁻¹ᵁ (U : A.Opens))
          (s : Γ(A, N ⁻¹ᵁ (U : A.Opens))),
          Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ρ U s) =
            ρ U' ((A.presheaf.map (homOfLE hle).op).hom s))
      (hinj : ∀ U : A.affineOpens, Function.Injective (N.app (U : A.Opens)).hom)
      (hcoinv : ∀ (U : A.affineOpens) (s : Γ(A, N ⁻¹ᵁ (U : A.Opens))),
          ρ U s = s ⊗ₜ[K] (1 : H) → s ∈ Set.range (N.app (U : A.Opens)).hom)

      (φ : A ⟶ A) (hφN : φ ≫ N = N ≫ φ) (φH : H →ₐ[K] H)
      (hequiv : ∀ (U W : A.affineOpens) (hle : N ⁻¹ᵁ (W : A.Opens) ≤ φ ⁻¹ᵁ (N ⁻¹ᵁ (U : A.Opens))),
        ∃ Ξ : Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H →+* Γ(A, N ⁻¹ᵁ (W : A.Opens)) ⊗[K] H,
          (∀ s : Γ(A, N ⁻¹ᵁ (U : A.Opens)),
              Ξ (s ⊗ₜ[K] (1 : H)) = (φ.appLE (N ⁻¹ᵁ (U : A.Opens)) (N ⁻¹ᵁ (W : A.Opens)) hle).hom s ⊗ₜ[K] (1 : H)) ∧
          (∀ x : H, Ξ ((1 : Γ(A, N ⁻¹ᵁ (U : A.Opens))) ⊗ₜ[K] x) = (1 : Γ(A, N ⁻¹ᵁ (W : A.Opens))) ⊗ₜ[K] φH x) ∧
          (∀ s : Γ(A, N ⁻¹ᵁ (U : A.Opens)),
              Ξ (ρ U s) = ρ W ((φ.appLE (N ⁻¹ᵁ (U : A.Opens)) (N ⁻¹ᵁ (W : A.Opens)) hle).hom s)))

      (𝒦 𝒲 : A.OrderedAffineCover) (lam lam' : 𝒲.ι → 𝒦.ι)
      (hlam : ∀ w, 𝒲.U w ≤ φ ⁻¹ᵁ 𝒦.U (lam w)) (hlam' : ∀ w, 𝒲.U w ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (lam' w))

      (h h' : H) (hh' : φH h = h')
      (S S' : ∀ i : 𝒦.ι, Γ(A, N ⁻¹ᵁ 𝒦.U i))
      (hS : ∀ i : 𝒦.ι, ρ ⟨𝒦.U i, 𝒦.isAffineOpen i⟩ (S i) = S i ⊗ₜ[K] (1 : H) + (1 : Γ(A, N ⁻¹ᵁ 𝒦.U i)) ⊗ₜ[K] h)
      (hS' : ∀ i : 𝒦.ι, ρ ⟨𝒦.U i, 𝒦.isAffineOpen i⟩ (S' i) = S' i ⊗ₜ[K] (1 : H) + (1 : Γ(A, N ⁻¹ᵁ 𝒦.U i)) ⊗ₜ[K] h')
      (c c' : (OModulePresheaf.unit f).cochain 𝒦 1)
      (hc : ∀ t : 𝒦.Idx 1, (N.app (𝒦.inter t)).hom (c t) =
        (A.presheaf.map (homOfLE (N.preimage_mono (𝒦.inter_le t 0))).op).hom (S (t.1 0)) -
          (A.presheaf.map (homOfLE (N.preimage_mono (𝒦.inter_le t 1))).op).hom (S (t.1 1)))
      (hc' : ∀ t : 𝒦.Idx 1, (N.app (𝒦.inter t)).hom (c' t) =
        (A.presheaf.map (homOfLE (N.preimage_mono (𝒦.inter_le t 0))).op).hom (S' (t.1 0)) -
          (A.presheaf.map (homOfLE (N.preimage_mono (𝒦.inter_le t 1))).op).hom (S' (t.1 1))),
    OModulePresheaf.unitPullback (πX := f) φ 𝒲 𝒦 lam hlam 1 c -
        OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒲 𝒦 lam' hlam' 1 c' ∈
      LinearMap.range ((OModulePresheaf.unit f).d 𝒲 0) := by sorry
