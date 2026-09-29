-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_of_isRegluingBy_of_isPullback
-- name    : GoodReductionJacobian.BareDeformation.exists_isRegluingBy_of_isRegluingBy_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/29b8dec1-63ac-5cac-8485-1c6d98ea5d67
-- title:
--   Re-gluing commutes with base change along a retraction
-- statement:
--   Let $B'$, $B$, $B_1$ be commutative rings with $B_1$ an algebra over both $B'$ and $B$, and let $\varphi : B' \to B$ be a ring homomorphism compatible with these structures, in the sense that the structure map $B \to B_1$ composed after $\varphi$ equals the structure map $B' \to B_1$. Fix a scheme $A_1$, a morphism $f_1 : A_1 \to \operatorname{Spec} B_1$ and a relative group law $L_1$ on $f_1$ over $B_1$, and let $D_0$, $D_0'$ be bare deformations of $(f_1,L_1)$ over $B$ and over $B'$ respectively (each consisting of a scheme, a structure morphism to the spectrum of its base, a commutative relative group law, an abelian-scheme property bundle, and a morphism from $A_1$ making the base-change square cartesian and respecting the group laws). Assume given an affine morphism $h_0 : D_0'.A \to D_0.A$ and a morphism $k : D_0.A \to D_0'.A$ with $k$ followed by $h_0$ the identity, such that the square formed by $k$, $D_0.f$, $D_0'.f$ and $\operatorname{Spec}\varphi$ is cartesian, and $D_0.g$ followed by $k$ equals $D_0'.g$. Let $\mathcal U$ be an ordered affine cover of $D_0.A$ (a finite linearly ordered family of affine opens with supremum $\top$), and let $\mathcal U' = \mathcal U.\mathrm{comap}\,h_0$ be the cover of $D_0'.A$ by the preimages $h_0^{-1}(\mathcal U.U\,i)$, with the same index type. Suppose given, for each strictly monotone pair $s$ of indices, a morphism $r_s$ from the intersection $\mathcal U.\mathrm{inter}\,s$ to $\mathcal U'.\mathrm{inter}\,s$ such that $r_s$ followed by the inclusion of $\mathcal U'.\mathrm{inter}\,s$ equals the inclusion of $\mathcal U.\mathrm{inter}\,s$ followed by $k$, and a self-isomorphism $\sigma_s$ of each $\mathcal U'.\mathrm{inter}\,s$. Suppose a bare deformation $P$ over $B'$ satisfies $D_0'.\mathrm{IsRegluingBy}\ \mathcal U'\ \sigma\ P$, i.e. each $\sigma_s$ is a morphism over $\operatorname{Spec} B'$, fixes the restriction of $D_0'.g$ to $\mathcal U'.\mathrm{inter}\,s$, and there are open immersions of the $\mathcal U'.U\,i$ into $P.A$ over $D_0'.f$, jointly surjective on points, compatible with $D_0'.g$ and $P.g$, and satisfying the $\sigma$-twisted overlap condition on each pair. Finally let $D_\varphi$ be a bare deformation over $B$ with a morphism $h : D_\varphi.A \to P.A$ making the square with $D_\varphi.f$, $P.f$ and $\operatorname{Spec}\varphi$ cartesian and with $D_\varphi.g$ followed by $h$ equal to $P.g$. The conclusion is that there exists a family of self-isomorphisms $\tau_s$ of the intersections $\mathcal U.\mathrm{inter}\,s$ such that $D_0.\mathrm{IsRegluingBy}\ \mathcal U\ \tau\ D_\varphi$ holds and, for every $s$, $\tau_s$ followed by $r_s$ equals $r_s$ followed by $\sigma_s$.
--
--   This is the base-change compatibility of the re-gluing construction for bare deformations: a deformation re-glued over $B'$ by overlap automorphisms $\sigma$, when pulled back along $\varphi : B' \to B$, is re-glued from the pulled-back deformation by the induced automorphisms $\tau$, compatibly with the comparison maps $r_s$ on overlaps. It is used in the analysis of re-glued deformations via tangent coordinates, notably by [`GoodReductionJacobian.BareDeformation.isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul`](thm.html#GoodReductionJacobian.BareDeformation.isShiftBy_add_smul_of_isRegluingBy_of_isTangentCoordsOfPairAt_add_smul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_of_isRegluingBy_of_isPullback.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld IsLocalRing
open scoped TensorProduct

theorem GoodReductionJacobian.BareDeformation.exists_isRegluingBy_of_isRegluingBy_of_isPullback
    (B' B B₁ : Type) [CommRing B'] [CommRing B] [CommRing B₁] [Algebra B' B₁] [Algebra B B₁]
    (φ : B' →+* B) (hφ : (algebraMap B B₁).comp φ = algebraMap B' B₁)
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (D₀ : BareDeformation f₁ L₁ B) (D₀' : BareDeformation f₁ L₁ B')
    (h₀ : D₀'.A ⟶ D₀.A) [IsAffineHom h₀]
    (k : D₀.A ⟶ D₀'.A) (hk : k ≫ h₀ = 𝟙 D₀.A)
    (hkc : IsPullback k D₀.f D₀'.f (Spec.map (CommRingCat.ofHom φ))) (hkg : D₀.g ≫ k = D₀'.g)
    (𝒰 : D₀.A.OrderedAffineCover)
    (r : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑((𝒰.comap h₀).inter s)))
    (hr : ∀ s : 𝒰.Idx 1, r s ≫ ((𝒰.comap h₀).inter s).ι = (𝒰.inter s).ι ≫ k)
    (σ : ∀ s : (𝒰.comap h₀).Idx 1, ((↑((𝒰.comap h₀).inter s) : Scheme.{0}) ≅ ↑((𝒰.comap h₀).inter s)))
    (P : BareDeformation f₁ L₁ B') (hP : D₀'.IsRegluingBy (𝒰.comap h₀) σ P)
    (Dφ : BareDeformation f₁ L₁ B) (h : Dφ.A ⟶ P.A)
    (hc : IsPullback h Dφ.f P.f (Spec.map (CommRingCat.ofHom φ))) (hg : Dφ.g ≫ h = P.g) :
    ∃ τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)),
      D₀.IsRegluingBy 𝒰 τ Dφ ∧ ∀ s : 𝒰.Idx 1, (τ s).hom ≫ r s = r s ≫ (σ s).hom := by sorry
