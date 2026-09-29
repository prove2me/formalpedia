-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_forall_subsingleton_HSucc_pullback_of_subsingleton_HSucc_closedFibre
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_forall_subsingleton_HSucc_pullback_of_subsingleton_HSucc_closedFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/20b4c4ad-52c1-5c1e-97e5-1fb7a5b61cf9
-- title:
--   Higher Čech vanishing spreads from the closed geometric fibre
-- statement:
--   Let $R$ be a noetherian local ring, let $f : A \to \operatorname{Spec} R$ be a morphism of schemes, and let `hA` assert the four properties packaged by `AbelianSchemePropertyBundle`: $f$ is smooth, $f$ is proper, the set-theoretic fibre of $f$ over each point of $\operatorname{Spec} R$ is connected, and $f$ carries a relative group law (a functorial group structure on the sections of $f$ over each $\operatorname{Spec} R$-scheme). Let $\mathcal L$ be an $\mathcal O_A$-module which is invertible in the sense that every point of $A$ has an open neighbourhood $U$ over which the restriction of $\mathcal L$ is isomorphic to the unit module of $U$. Let $k_0$ be an algebraically closed field and $s_0 : R \to k_0$ a ring homomorphism with kernel the maximal ideal of $R$, so that $\operatorname{Spec} k_0 \to \operatorname{Spec} R$ is a geometric point over the closed point. Let $\mathcal U$ be an ordered affine cover of the fibre product $A \times_{\operatorname{Spec} R} \operatorname{Spec} k_0$, that is, a finite linearly ordered family of affine opens whose supremum is the whole space. Assume that for every $i \in \mathbb{N}$ the module $\ker d^{i+1} / \operatorname{im} d^{i}$ of the Čech complex of the presheaf of sections of the pullback of $\mathcal L$ to that fibre product, taken with respect to $\mathcal U$ and viewed over $k_0$ via the projection to $\operatorname{Spec} k_0$, is a subsingleton; thus all higher Čech cohomology of $\mathcal L$ on the geometric closed fibre vanishes for this cover. Then for every field $K$ which is an $R$-algebra there exists an ordered affine cover $\mathcal W$ of $A \times_{\operatorname{Spec} R} \operatorname{Spec} K$ such that for every $i \in \mathbb{N}$ the corresponding module $\ker d^{i+1} / \operatorname{im} d^{i}$ for the pullback of $\mathcal L$ to $A \times_{\operatorname{Spec} R} \operatorname{Spec} K$ is a subsingleton.
--
--   This is the cohomology-and-base-change statement for an invertible module on an abelian scheme over a noetherian local base: vanishing of the higher cohomology on the geometric closed fibre propagates to the fibre over an arbitrary field-valued point, the vanishing being expressed through the Čech complex of a finite ordered affine cover. It is used in the computation of the dimension of the space of global sections on geometric fibres, via [`GoodReductionJacobian.AbelianSchemePropertyBundle.geomFibreH0Finrank_eq_of_subsingleton_HSucc_closedFibre`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.geomFibreH0Finrank_eq_of_subsingleton_HSucc_closedFibre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_forall_subsingleton_HSucc_pullback_of_subsingleton_HSucc_closedFibre.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_forall_subsingleton_HSucc_pullback_of_subsingleton_HSucc_closedFibre
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (hA : AbelianSchemePropertyBundle R f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (s₀ : R →+* k₀) (hs₀ : RingHom.ker s₀ = IsLocalRing.maximalIdeal R)
    (𝒰 : (pullback f (Spec.map (CommRingCat.ofHom s₀))).OrderedAffineCover)
    (hvan : ∀ i : ℕ, Subsingleton
      ((OModulePresheaf.ofModules (pullback.snd f (Spec.map (CommRingCat.ofHom s₀)))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom s₀)))).obj 𝓛)).HSucc 𝒰 i))
    (K : Type) [Field K] [Algebra R K] :
    ∃ 𝒲 : (pullback f (Scheme.TwoAffineOpenCover.specMap R K)).OrderedAffineCover, ∀ i : ℕ,
      Subsingleton ((OModulePresheaf.ofModules (pullback.snd f (Scheme.TwoAffineOpenCover.specMap R K))
        ((Scheme.Modules.pullback (pullback.fst f (Scheme.TwoAffineOpenCover.specMap R K))).obj 𝓛)).HSucc 𝒲 i) := by sorry
