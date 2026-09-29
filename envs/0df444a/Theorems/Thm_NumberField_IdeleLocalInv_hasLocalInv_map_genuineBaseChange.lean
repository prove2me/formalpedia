-- Prove2me | Theorems.Thm_NumberField_IdeleLocalInv_hasLocalInv_map_genuineBaseChange
-- name    : NumberField.IdeleLocalInv.hasLocalInv_map_genuineBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/8e3012fd-3f6e-5fc8-bf64-659a798de4e8
-- title:
--   Local invariants survive genuine adèlic base change
-- statement:
--   Let $E$, $K$, $K''$ be number fields with $E$-algebra structures on $K$ and $K''$, a $K$-algebra structure on $K''$ forming a scalar tower over $E$, and $K/E$, $K''/E$ Galois. Let $D$ be an idèle Galois descent datum for $K/E$, that is a monoid homomorphism from $\mathrm{Gal}(K/E)$ to the ring automorphisms of the adèle ring $\mathbb{A}_K$ of $K$ which is continuous and compatible with the structure map $K \to \mathbb{A}_K$, and suppose the given multiplicative-distributive action of $\mathrm{Gal}(K/E)$ on $\mathbb{A}_K^\times$ is the one induced by $D$ on units; let $D''$ and the action on $\mathbb{A}_{K''}^\times$ satisfy the same for $K''/E$. Let $J$ be a morphism of $\mathrm{Gal}(K''/E)$-representations from the restriction of $\mathbb{A}_K^\times$ along $\mathrm{AlgEquiv.restrictNormalHom}$ $\mathrm{Gal}(K''/E) \to \mathrm{Gal}(K/E)$ to $\mathbb{A}_{K''}^\times$, acting on elements as $\mathrm{Units.map}$ of the ring homomorphism $\beta$ of `genuineBaseChange K K''` (the adèle base change built from $\mathrm{genuine}\beta$ and the genuine identification $\mathbb{A}_K \otimes_K K'' \cong \mathbb{A}_{K''}$). Let $x \in H^2(\mathrm{Gal}(K/E), \mathbb{A}_K^\times)$, let $v$ be a nonzero prime of $\mathcal{O}_E$ and $t \in \mathbb{Q}/\mathbb{Z}$, and assume `HasLocalInv E K D hactI x v t`: there are representation morphisms realising, for every finite place $w$ of $K$, the $w$-coordinate map $\mathrm{finPart}\,w$ on idèle units as a morphism of representations of the decomposition group $\mathrm{decomp}\,E\,K\,w$; a place $w$ of $K$ contracting to $v$; a prime $q$ in $w$, a finite extension $L'$ of $\mathbb{Q}_q$ inside a fixed algebraic closure carrying a faithful action of $\mathrm{decomp}\,E\,K\,w$ trivial on $\mathbb{Q}_q$ and compatible with units, an equivariant ring isomorphism $\Phi \colon K_w \cong L'$, a finite subextension $K_0$ of $\mathbb{Q}_q$ which is exactly the fixed field of the group in $L'$, a morphism $\theta$ from $(L')^\times$ to $K_w^\times$ given by $\Phi^{-1}$, a class $u'$ in $H^2(\mathrm{decomp}\,E\,K\,w, (L')^\times)$ that is the local fundamental class for $L'/K_0$, and an integer $n$ with the image of $x$ in $H^2(\mathrm{decomp}\,E\,K\,w, K_w^\times)$ equal to $n$ times the image of $u'$ under $\theta$ and $t = n/\#\mathrm{decomp}\,E\,K\,w$. Then the corresponding predicate `HasLocalInv E K'' D'' hactI''` holds for the image of $x$ under the map on degree-$2$ group cohomology induced by the restriction homomorphism $\mathrm{Gal}(K''/E) \to \mathrm{Gal}(K/E)$ together with $J$, for the same $v$ and the same $t$.
--
--   This is the compatibility of the local invariant at a place $v$ of $E$ with passage from a Galois layer $K/E$ to a larger Galois layer $K''/E$ along the adèlic base change: the invariant, normalised by division by the order of the decomposition group, is unchanged even though both the decomposition group and the degree of the local extension grow. It is used in the construction of idèle classes with prescribed local invariants from $S$-unit cocycle data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_IdeleLocalInv_hasLocalInv_map_genuineBaseChange.lean

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand
open M4aHerbrand.GenuineDescent
open scoped NumberField.PlaceDecomp

theorem NumberField.IdeleLocalInv.hasLocalInv_map_genuineBaseChange
    (E K K'' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K''] [NumberField K'']
    [Algebra E K] [Algebra K K''] [Algebra E K''] [IsScalarTower E K K''] [IsGalois E K] [IsGalois E K'']

    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (D'' : IdeleGaloisDescent (𝓞 K'') E K'')
    [MulDistribMulAction (K'' ≃ₐ[E] K'') (AdeleRing (𝓞 K'') K'')ˣ]
    (hactI'' : ∀ (g : K'' ≃ₐ[E] K'') (x : (AdeleRing (𝓞 K'') K'')ˣ), g • x = D''.unitsAct g x)

    (J : Rep.res (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶ (Rep.ofMulDistribMulAction (K'' ≃ₐ[E] K'') (AdeleRing (𝓞 K'') K'')ˣ))
    (hJ : ∀ z : (AdeleRing (𝓞 K) K)ˣ, Additive.toMul (J.hom (Additive.ofMul z)) =
      Units.map (genuineBaseChange K K'').β.toMonoidHom z)
    (x : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) 2) (v : HeightOneSpectrum (𝓞 E)) (t : AddCircle (1 : ℚ))
    (h : NumberField.IdeleLocalInv.HasLocalInv E K D hactI x v t) :
    NumberField.IdeleLocalInv.HasLocalInv E K'' D'' hactI''
      ((groupCohomology.map (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) J 2).hom x) v t := by sorry
