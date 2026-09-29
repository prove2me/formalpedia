-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geomFibreH0Finrank_eq_of_subsingleton_HSucc_closedFibre
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.geomFibreH0Finrank_eq_of_subsingleton_HSucc_closedFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/84af2083-5ecc-5c30-a56c-df0bd2d9275d
-- title:
--   Constancy of geometric-fibre h⁰ over a local base
-- statement:
--   Let $R$ be a commutative local noetherian ring, let $A$ be a scheme and $f : A \to \operatorname{Spec} R$ a morphism (everything in the bottom universe) satisfying `AbelianSchemePropertyBundle`, i.e. $f$ is smooth, proper, each set-theoretic fibre of the underlying map is connected, and there exists a relative group law on $f$ (a functorial group structure on sections over $\operatorname{Spec} R$). Let $\mathcal L$ be a module on $A$ which is invertible in the sense that every point has an open neighbourhood $U$ on which the restriction of $\mathcal L$ is isomorphic to the unit module of $U$. Let $k_0$ be an algebraically closed field and $s_0 : R \to k_0$ a ring map whose kernel is the maximal ideal of $R$, and let $\mathcal U$ be a finite linearly ordered family of affine opens covering the fibre product $A \times_{\operatorname{Spec} R} \operatorname{Spec} k_0$. Assume that for every $i \in \mathbb N$ the $i$-th higher cohomology group $\ker d^{i+1} / \operatorname{im} d^i$ of the Čech-type complex of the $\mathcal O$-module presheaf of sections of the pullback of $\mathcal L$ to this geometric closed fibre, over the cover $\mathcal U$, is a subsingleton. Then for every algebraically closed field $k$ and every ring map $s_k : R \to k$ one has $\dim_k H^0$ of the pullback of $\mathcal L$ to $A \times_{\operatorname{Spec} R} \operatorname{Spec} k$ equal to the corresponding dimension over $k_0$ for $s_0$.
--
--   This is the degree-zero case of cohomology and base change over a local base: vanishing of the higher cohomology of $\mathcal L$ on the geometric closed fibre forces $h^0$ of the geometric fibres to be constant on $\operatorname{Spec} R$. It is used to propagate positivity of $h^0$ from the closed fibre to all geometric fibres, e.g. in the treatment of canonical polarisation data for fake elliptic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geomFibreH0Finrank_eq_of_subsingleton_HSucc_closedFibre.lean

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

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.geomFibreH0Finrank_eq_of_subsingleton_HSucc_closedFibre
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of R)) (hA : AbelianSchemePropertyBundle R f)
    (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
    (k₀ : Type) [Field k₀] [IsAlgClosed k₀] (s₀ : R →+* k₀) (hs₀ : RingHom.ker s₀ = IsLocalRing.maximalIdeal R)
    (𝒰 : (pullback f (Spec.map (CommRingCat.ofHom s₀))).OrderedAffineCover)
    (hvan : ∀ i : ℕ, Subsingleton
      ((OModulePresheaf.ofModules (pullback.snd f (Spec.map (CommRingCat.ofHom s₀)))
        ((Scheme.Modules.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom s₀)))).obj 𝓛)).HSucc 𝒰 i))
    (k : Type) [Field k] [IsAlgClosed k] (sk : R →+* k) :
    Scheme.Modules.geomFibreH0Finrank f 𝓛 k sk = Scheme.Modules.geomFibreH0Finrank f 𝓛 k₀ s₀ := by sorry
