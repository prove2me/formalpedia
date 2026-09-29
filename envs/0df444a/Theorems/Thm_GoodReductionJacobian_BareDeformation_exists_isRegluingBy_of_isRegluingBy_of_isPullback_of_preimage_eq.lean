-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_of_isRegluingBy_of_isPullback_of_preimage_eq
-- name    : GoodReductionJacobian.BareDeformation.exists_isRegluingBy_of_isRegluingBy_of_isPullback_of_preimage_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/c5fe33a5-6b23-5e4b-83c4-e510504317a1
-- title:
--   Re-gluing commutes with base change along φ
-- statement:
--   Fix a commutative ring $S$, a scheme $A_S$ with a morphism $f_S\colon A_S\to\operatorname{Spec} S$ and a relative group law $L_S$ on $f_S$, and a commutative ring $B$ with a $B$-algebra structure on $S$. Let $D_0$ be a bare deformation of $(f_S,L_S)$ to $B$ — a scheme $D_0.A$ with structure morphism $D_0.f$ to $\operatorname{Spec} B$, a commutative relative group law, the property bundle (smooth, proper, connected fibres, a group law), and a morphism $D_0.g\colon A_S\to D_0.A$ making a cartesian square over $\operatorname{Spec}$ of $B\to S$ and compatible with multiplication. Let $\mathcal U$ be an ordered affine cover of $D_0.A$ (a finite linearly ordered index type, affine opens $U_i$ with supremum $\top$), and for each strictly monotone $s\colon \mathrm{Fin}\,2\to\mathcal U.\iota$ let $\tau_s$ be a self-isomorphism of the overlap $\mathcal U.\mathrm{inter}\,s=U_{s(0)}\sqcap U_{s(1)}$. Assume a further bare deformation $D$ with `D₀.IsRegluingBy 𝒰 τ D`: each $\tau_s$ lies over $D_0.f$, each $\tau_s$ fixes the restriction of $D_0.g$ to the overlap, and there are open immersions $\iota_i\colon U_i\to D.A$ over $D_0.f$, jointly surjective on points, compatible with $D_0.g$ and $D.g$, and satisfying the gluing identity $\mathrm{hom}_{\le}\mathbin{;}\iota_{s(0)}=\tau_s\mathbin{;}\mathrm{hom}_{\le}\mathbin{;}\iota_{s(1)}$ on each overlap. Let $\varphi\colon B\to B$ be a ring endomorphism, let $k_0\colon D_0.A\to D_0.A$ make $D_0.A$ a base change of itself along $\operatorname{Spec}\varphi$ (cartesian square $k_0\mathbin{;}D_0.f=D_0.f\mathbin{;}\operatorname{Spec}\varphi$), with $D_0.g\mathbin{;}k_0=D_0.g$ and $k_0^{-1}(U_a)=U_a$ for all $a$; let $D^{\varphi}$ be a bare deformation with $h\colon D^{\varphi}.A\to D.A$ cartesian over $\operatorname{Spec}\varphi$ and $D^{\varphi}.g\mathbin{;}h=D.g$; and assume each overlap is contained in its $k_0$-preimage (so that the restriction $k_0|$ of $k_0$ to the overlap is defined). Then there exist self-isomorphisms $\tau'_s$ of the overlaps with $\tau'_s$ followed by $k_0|$ equal to $k_0|$ followed by $\tau_s$ for every $s$, and such that `D₀.IsRegluingBy 𝒰 τ' Dφ` holds.
--
--   The statement says that re-gluing a bare deformation along overlap automorphisms is compatible with base change along a ring endomorphism $\varphi$ of $B$, provided the reference deformation $D_0$ carries a chart-preserving self-base-change $k_0$ over $\operatorname{Spec}\varphi$: the base-changed deformation $D^{\varphi}$ is re-glued from $D_0$ on the same cover, by the automorphisms obtained from the $\tau_s$ by base change along $k_0$. It is used in the comparison of re-glued deformations with tangent coordinates at a pair of points under such a base change.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_of_isRegluingBy_of_isPullback_of_preimage_eq.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem GoodReductionJacobian.BareDeformation.exists_isRegluingBy_of_isRegluingBy_of_isPullback_of_preimage_eq
    {S : Type} [CommRing S] {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S)} {Lₛ : RelativeGroupLaw S fₛ}
    {B : Type} [CommRing B] [Algebra B S]
    (D₀ : BareDeformation fₛ Lₛ B) (𝒰 : D₀.A.OrderedAffineCover)
    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D : BareDeformation fₛ Lₛ B) (hD : D₀.IsRegluingBy 𝒰 τ D)
    (φ : B →+* B)
    (k₀ : D₀.A ⟶ D₀.A) (hk₀ : IsPullback k₀ D₀.f D₀.f (Spec.map (CommRingCat.ofHom φ)))
    (hk₀g : D₀.g ≫ k₀ = D₀.g) (hk₀U : ∀ a : 𝒰.ι, k₀ ⁻¹ᵁ 𝒰.U a = 𝒰.U a)
    (Dφ : BareDeformation fₛ Lₛ B) (h : Dφ.A ⟶ D.A)
    (hh : IsPullback h Dφ.f D.f (Spec.map (CommRingCat.ofHom φ))) (hhg : Dφ.g ≫ h = D.g)
    (hle : ∀ s : 𝒰.Idx 1, 𝒰.inter s ≤ k₀ ⁻¹ᵁ 𝒰.inter s) :
    ∃ τ' : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)),
      (∀ s : 𝒰.Idx 1, (τ' s).hom ≫ k₀.resLE (𝒰.inter s) (𝒰.inter s) (hle s) =
        k₀.resLE (𝒰.inter s) (𝒰.inter s) (hle s) ≫ (τ s).hom) ∧
      D₀.IsRegluingBy 𝒰 τ' Dφ := by sorry
