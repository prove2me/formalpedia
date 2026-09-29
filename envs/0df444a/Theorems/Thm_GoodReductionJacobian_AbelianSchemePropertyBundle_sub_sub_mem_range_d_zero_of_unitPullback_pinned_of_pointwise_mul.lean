-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_sub_sub_mem_range_d_zero_of_unitPullback_pinned_of_pointwise_mul
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.sub_sub_mem_range_d_zero_of_unitPullback_pinned_of_pointwise_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/d2a05dd9-945d-555d-bea1-d8d4043297b3
-- title:
--   Additivity in the endomorphism of degree-one Čech pull-back
-- statement:
--   Let $k$ be a field, $A$ a scheme and $f\colon A\to\operatorname{Spec}k$ a morphism, equipped with a relative group law $L$ (a functorial group structure on the sets $\{P\colon T\to A \mid P\circ f=t\}$ of points over $k$-schemes $t\colon T\to\operatorname{Spec}k$, natural in $T$) and with the property bundle `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, each fibre $f^{-1}(s)$ is connected, and $f$ admits some relative group law. Let $\mathcal K$ be an ordered affine cover of $A$ (a finite linearly ordered family of affine opens with supremum $\top$) and let $\varphi,\psi,\chi\colon A\to A$ satisfy $\varphi\circ f=\psi\circ f=\chi\circ f=f$, with $P$ followed by $\chi$ equal to the $L$-product of $P$ followed by $\varphi$ and $P$ followed by $\psi$, for every point $P$ of $A$ over every $k$-scheme. Let $\mathcal V_1,\mathcal V_2,\mathcal V_3$ be ordered affine covers of $A$ with index maps $\lambda_i,\lambda_i'\colon\mathcal V_i.\iota\to\mathcal K.\iota$ such that each $\mathcal V_i.U(v)$ lies in the preimage of $\mathcal K.U(\lambda_i v)$ under $\varphi,\psi,\chi$ respectively, and in $\mathcal K.U(\lambda_i' v)$ (the preimage under $\mathrm{id}_A$). Let $z,z_1,z_2,z_3$ be degree-one Čech cochains of the structure-sheaf presheaf `OModulePresheaf.unit f` on $\mathcal K$, all annihilated by the differential $d$ in degree one, and suppose that the signed reindexed pull-back `unitPullback` of $z$ along $\varphi$ via $\lambda_1$ minus that of $z_1$ along $\mathrm{id}_A$ via $\lambda_1'$ lies in the image of $d\colon C^0(\mathcal V_1)\to C^1(\mathcal V_1)$, and likewise for $\psi,z_2,\lambda_2,\lambda_2'$ on $\mathcal V_2$ and for $\chi,z_3,\lambda_3,\lambda_3'$ on $\mathcal V_3$. Then $z_3-z_1-z_2$ lies in the image of $d\colon C^0(\mathcal K)\to C^1(\mathcal K)$.
--
--   This is the primitivity, or additivity in the endomorphism, of degree-one coherent cohomology classes on an abelian scheme, stated in terms of cocycles on a fixed ordered affine cover together with cocycles pinned to $\varphi$, $\psi$ and $\chi$ on refinements. It feeds the construction of the algebra homomorphism from an endomorphism acting on pinned degree-one classes, in [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_endo_algHom_pinned_unitPullback_of_cls_cup`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_endo_algHom_pinned_unitPullback_of_cls_cup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_sub_sub_mem_range_d_zero_of_unitPullback_pinned_of_pointwise_mul.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.sub_sub_mem_range_d_zero_of_unitPullback_pinned_of_pointwise_mul
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (L : RelativeGroupLaw k f) (hA : AbelianSchemePropertyBundle k f) (𝒦 : A.OrderedAffineCover)
    (φ ψ χ : A ⟶ A) (hφ : φ ≫ f = f) (hψ : ψ ≫ f = f) (hχ : χ ≫ f = f)
    (hsum : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (P : SchemeHomOver t f),
        P.1 ≫ χ = (L.mul t ⟨P.1 ≫ φ, by rw [Category.assoc, hφ]; exact P.2⟩
          ⟨P.1 ≫ ψ, by rw [Category.assoc, hψ]; exact P.2⟩).1)

    (𝒱₁ : A.OrderedAffineCover) (lam₁ lam₁' : 𝒱₁.ι → 𝒦.ι)
    (hl₁ : ∀ v, 𝒱₁.U v ≤ φ ⁻¹ᵁ 𝒦.U (lam₁ v)) (hl₁' : ∀ v, 𝒱₁.U v ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (lam₁' v))
    (𝒱₂ : A.OrderedAffineCover) (lam₂ lam₂' : 𝒱₂.ι → 𝒦.ι)
    (hl₂ : ∀ v, 𝒱₂.U v ≤ ψ ⁻¹ᵁ 𝒦.U (lam₂ v)) (hl₂' : ∀ v, 𝒱₂.U v ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (lam₂' v))
    (𝒱₃ : A.OrderedAffineCover) (lam₃ lam₃' : 𝒱₃.ι → 𝒦.ι)
    (hl₃ : ∀ v, 𝒱₃.U v ≤ χ ⁻¹ᵁ 𝒦.U (lam₃ v)) (hl₃' : ∀ v, 𝒱₃.U v ≤ (𝟙 A) ⁻¹ᵁ 𝒦.U (lam₃' v))
    (z z₁ z₂ z₃ : (OModulePresheaf.unit f).cochain 𝒦 1)
    (hz : (OModulePresheaf.unit f).d 𝒦 1 z = 0) (hz₁ : (OModulePresheaf.unit f).d 𝒦 1 z₁ = 0)
    (hz₂ : (OModulePresheaf.unit f).d 𝒦 1 z₂ = 0) (hz₃ : (OModulePresheaf.unit f).d 𝒦 1 z₃ = 0)
    (h₁ : OModulePresheaf.unitPullback (πX := f) φ 𝒱₁ 𝒦 lam₁ hl₁ 1 z -
        OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱₁ 𝒦 lam₁' hl₁' 1 z₁
      ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱₁ 0))
    (h₂ : OModulePresheaf.unitPullback (πX := f) ψ 𝒱₂ 𝒦 lam₂ hl₂ 1 z -
        OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱₂ 𝒦 lam₂' hl₂' 1 z₂
      ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱₂ 0))
    (h₃ : OModulePresheaf.unitPullback (πX := f) χ 𝒱₃ 𝒦 lam₃ hl₃ 1 z -
        OModulePresheaf.unitPullback (πX := f) (𝟙 A) 𝒱₃ 𝒦 lam₃' hl₃' 1 z₃
      ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱₃ 0)) :
    z₃ - z₁ - z₂ ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒦 0) := by sorry
