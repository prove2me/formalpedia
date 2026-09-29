-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_mem_range_d_zero_of_unitPullback_section_mem_range
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.mem_range_d_zero_of_unitPullback_section_mem_range
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/bf7d4aae-dcee-579c-bec7-edcd4447ab62
-- title:
--   Čech H¹ of A×_k A detected by the two axis sections
-- statement:
--   Let $k$ be a field and let $f : A \to \operatorname{Spec} k$ be a morphism of schemes satisfying `AbelianSchemePropertyBundle`, i.e. $f$ is smooth and proper, every fibre of $f$ (as a subset of $A$ over a point of $\operatorname{Spec} k$) is connected, and $f$ admits a relative group law in the functor-of-points sense. Let $e$ be a section of $f$, and let $s_1, s_2 : A \to A \times_{\operatorname{Spec} k} A$ (the categorical pullback of $f$ along itself) be morphisms pinned down by $s_1 \circ \mathrm{pr}_1 = \mathrm{id}_A$, $s_1$ followed by $\mathrm{pr}_2$ equal to $e \circ f$, and symmetrically $s_2$ followed by $\mathrm{pr}_1$ equal to $e \circ f$ and $s_2$ followed by $\mathrm{pr}_2$ equal to $\mathrm{id}_A$; thus $s_1$ and $s_2$ are the two axis sections. Let $\mathcal W$ be an ordered affine cover of the pullback and $\mathcal V_1, \mathcal V_2$ ordered affine covers of $A$ (each given by a finite linearly ordered index type together with affine opens whose supremum is $\top$), and let $\lambda_i$ be index maps with $\mathcal V_i$ refining $\mathcal W$ along $s_i$, i.e. each $\mathcal V_i$-member contained in the $s_i$-preimage of the corresponding $\mathcal W$-member. Let $Z$ be a $1$-cochain for the presheaf `OModulePresheaf.unit` of structural sections on the pullback, relative to $\mathrm{pr}_1$ followed by $f$ — that is, a family of sections of $\mathcal O$ over the intersections indexed by increasing pairs in $\mathcal W$ — with $\mathrm{d}Z = 0$. If the signed reindexed pullbacks `OModulePresheaf.unitPullback` of $Z$ along $s_1$ and along $s_2$ lie in the image of $\mathrm{d}$ on $0$-cochains for $\mathcal V_1$ and $\mathcal V_2$ respectively, then $Z$ lies in the image of $\mathrm{d}$ on $0$-cochains for $\mathcal W$.
--
--   This is the degree-one Künneth statement for the structure sheaf of $A \times_k A$ in Čech form: a $1$-cocycle whose restrictions to the two axes $A \times e$ and $e \times A$ are coboundaries is itself a coboundary, so that $\check H^1(A \times_k A, \mathcal O)$ is detected by the two axis sections. It feeds the construction of isomorphisms from biextension/rigidity data for the relative Picard functor of an abelian scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_mem_range_d_zero_of_unitPullback_section_mem_range.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.mem_range_d_zero_of_unitPullback_section_mem_range
    (k : Type u) [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k))
    (hA : AbelianSchemePropertyBundle k f)

    (e : Spec (CommRingCat.of k) ⟶ A) (he : e ≫ f = 𝟙 _)
    (s₁ s₂ : A ⟶ pullback f f)
    (hs₁ : s₁ ≫ pullback.fst f f = 𝟙 A) (hs₁' : s₁ ≫ pullback.snd f f = f ≫ e)
    (hs₂ : s₂ ≫ pullback.fst f f = f ≫ e) (hs₂' : s₂ ≫ pullback.snd f f = 𝟙 A)

    (𝒲 : (pullback f f).OrderedAffineCover) (𝒱₁ 𝒱₂ : A.OrderedAffineCover)
    (lam₁ : 𝒱₁.ι → 𝒲.ι) (lam₂ : 𝒱₂.ι → 𝒲.ι)
    (hl₁ : ∀ v, 𝒱₁.U v ≤ s₁ ⁻¹ᵁ 𝒲.U (lam₁ v)) (hl₂ : ∀ v, 𝒱₂.U v ≤ s₂ ⁻¹ᵁ 𝒲.U (lam₂ v))

    (Z : (OModulePresheaf.unit (pullback.fst f f ≫ f)).cochain 𝒲 1)
    (hZ : (OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 1 Z = 0)
    (h₁ : OModulePresheaf.unitPullback (πX := f) s₁ 𝒱₁ 𝒲 lam₁ hl₁ 1 Z ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱₁ 0))
    (h₂ : OModulePresheaf.unitPullback (πX := f) s₂ 𝒱₂ 𝒲 lam₂ hl₂ 1 Z ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒱₂ 0)) :
    Z ∈ LinearMap.range ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 0) := by sorry
