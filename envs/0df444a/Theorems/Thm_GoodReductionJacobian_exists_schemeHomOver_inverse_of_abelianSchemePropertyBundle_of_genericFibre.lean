-- Prove2me | Theorems.Thm_GoodReductionJacobian_exists_schemeHomOver_inverse_of_abelianSchemePropertyBundle_of_genericFibre
-- name    : GoodReductionJacobian.exists_schemeHomOver_inverse_of_abelianSchemePropertyBundle_of_genericFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/38f8f0e9-7671-5d4a-b8fa-900410efa1e4
-- title:
--   Isomorphisms of generic fibres of abelian schemes extend uniquely
-- statement:
--   Let $R$ be a discrete valuation ring which is a domain, and let $K$ be a field that is an $R$-algebra and a fraction field of $R$. Let $f_1 : A_1 \to \operatorname{Spec} R$ and $f_2 : A_2 \to \operatorname{Spec} R$ be morphisms of schemes each satisfying `AbelianSchemePropertyBundle`, i.e. each is smooth and proper, the preimage under the underlying map of each point of $\operatorname{Spec} R$ is connected, and a `RelativeGroupLaw` over $R$ exists for it (a functorial group structure on sections over $R$-schemes). Write $(A_i)_K \to \operatorname{Spec} K$ for the second projection of the pullback of $f_i$ along $\operatorname{Spec}(K) \to \operatorname{Spec}(R)$ induced by $R \to K$. Suppose given $\varphi_K : (A_1)_K \to (A_2)_K$ and $\psi_K : (A_2)_K \to (A_1)_K$, each commuting with the structure morphisms to $\operatorname{Spec} K$, with $\varphi_K$ followed by $\psi_K$ and $\psi_K$ followed by $\varphi_K$ both the identity. The conclusion asserts the existence of $\varphi : A_1 \to A_2$ over $\operatorname{Spec} R$ and $\psi : A_2 \to A_1$ over $\operatorname{Spec} R$ whose generic-fibre restrictions (the pullback lifts) are exactly $\varphi_K$ and $\psi_K$, such that $\varphi$ followed by $\psi$ is $\mathrm{id}_{A_1}$, $\psi$ followed by $\varphi$ is $\mathrm{id}_{A_2}$, and $\varphi$ is the unique $R$-morphism $A_1 \to A_2$ restricting to $\varphi_K$.
--
--   This is the statement that an abelian scheme over a discrete valuation ring is the Néron model of its generic fibre, in the form needed to transport an isomorphism defined over $K$ to one over $R$; uniqueness is asserted for $\varphi$ only. It is used in the construction of good-reduction models of Jacobians of modular curves, via [`ModularCurve.exists_pointsDict_pullback_snd_ratLocalizedAt_of_dRModelPackage_of_representsRelSubPic`](thm.html#ModularCurve.exists_pointsDict_pullback_snd_ratLocalizedAt_of_dRModelPackage_of_representsRelSubPic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_exists_schemeHomOver_inverse_of_abelianSchemePropertyBundle_of_genericFibre.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.exists_schemeHomOver_inverse_of_abelianSchemePropertyBundle_of_genericFibre
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {A₁ A₂ : Scheme.{u}} {f₁ : A₁ ⟶ Spec (CommRingCat.of R)} {f₂ : A₂ ⟶ Spec (CommRingCat.of R)}
    (h₁ : AbelianSchemePropertyBundle R f₁) (h₂ : AbelianSchemePropertyBundle R f₂)
    (φK : SchemeHomOver (pullback.snd f₁ (specGenericFibreInclusion R K))
      (pullback.snd f₂ (specGenericFibreInclusion R K)))
    (ψK : SchemeHomOver (pullback.snd f₂ (specGenericFibreInclusion R K))
      (pullback.snd f₁ (specGenericFibreInclusion R K)))
    (hφψ : φK.1 ≫ ψK.1 = 𝟙 _) (hψφ : ψK.1 ≫ φK.1 = 𝟙 _) :
    ∃ (φ : SchemeHomOver f₁ f₂) (ψ : SchemeHomOver f₂ f₁),
      genericFibreRestrict R K f₂ f₁ φ = φK ∧ genericFibreRestrict R K f₁ f₂ ψ = ψK ∧
      φ.1 ≫ ψ.1 = 𝟙 A₁ ∧ ψ.1 ≫ φ.1 = 𝟙 A₂ ∧
      (∀ φ' : SchemeHomOver f₁ f₂, genericFibreRestrict R K f₂ f₁ φ' = φK → φ' = φ) := by sorry
