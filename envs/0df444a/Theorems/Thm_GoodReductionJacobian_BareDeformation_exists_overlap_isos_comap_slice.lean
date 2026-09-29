-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_overlap_isos_comap_slice
-- name    : GoodReductionJacobian.BareDeformation.exists_overlap_isos_comap_slice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/4b2a122b-dfee-567f-a817-8e2e9dd1aa81
-- title:
--   Universal overlap automorphism over a triple fibre product of bases
-- statement:
--   Let $B'$, $B$, $B_1$ be commutative rings with $B_1$ an algebra over both $B'$ and $B$, with $B\to B_1$ surjective, and let $\delta\colon B\to B'$ satisfy $B'\to B_1$ composed after $\delta$ equals $B\to B_1$. Let $p_0,p_1,p_2\colon B'\to B$ be ring maps, each a retraction of $\delta$ ($p_i\circ\delta=\mathrm{id}_B$) and each compatible with the maps to $B_1$ ($B\to B_1$ after $p_i$ equals $B'\to B_1$), such that the $p_i$ are jointly injective and such that any triple $b_0,b_1,b_2\in B$ with equal images in $B_1$ is $(p_0x,p_1x,p_2x)$ for some $x\in B'$; thus $B'$ presents the triple fibre product $B\times_{B_1}B\times_{B_1}B$. Let $f_1\colon A_1\to\operatorname{Spec}B_1$ carry a relative group law $L_1$, and let $D_0$, $D_0'$ be bare deformations of $(f_1,L_1)$ over $B$ and over $B'$ respectively — each a scheme with structure morphism to the spectrum of its base, a commutative relative group law, an abelian-scheme property bundle, and a morphism from $A_1$ exhibiting $f_1$ as the base change, compatible with multiplication — with $D_0.f$ separated. Let $h'\colon D_0'.A\to D_0.A$ be an affine morphism making the square with $D_0'.f$, $D_0.f$ and $\operatorname{Spec}\delta$ cartesian, with $D_0'.g$ followed by $h'$ equal to $D_0.g$, and let $k_0,k_1,k_2\colon D_0.A\to D_0'.A$ be sections of $h'$ ($k_i$ followed by $h'$ is the identity) lying over $\operatorname{Spec}p_i$ ($k_i$ followed by $D_0'.f$ equals $D_0.f$ followed by $\operatorname{Spec}p_i$). Let $\mathcal U$ be an ordered affine cover of $D_0.A$, that is, a finite linearly ordered family of affine opens with supremum $\top$, and write $U_s$ for the intersection indexed by a strictly monotone pair $s$. Given two families $\tau,\tau'$ of automorphisms of the schemes $U_s$, each lying over $\operatorname{Spec}B$ (composition with $U_s\hookrightarrow D_0.A$ followed by $D_0.f$ unchanged) and fixing the restriction of $D_0.g$ to $U_s$, the conclusion asserts a family $\sigma$ of automorphisms of the corresponding overlaps $U'_s$ of the cover $\mathcal U.\mathrm{comap}\,h'$ by the preimages $h'^{-1}(\mathcal U.U i)$, lying over $\operatorname{Spec}B'$ and fixing the restriction of $D_0'.g$, whose three slices along the $k_i$ are $\mathrm{id}$, $\tau_s$ and $\tau'_s$: for every $s$ and every $\kappa\colon U_s\to U'_s$ with $\kappa$ followed by $U'_s\hookrightarrow D_0'.A$ equal to $U_s\hookrightarrow D_0.A$ followed by $k_0$ one has $\kappa\circ\ldots$, precisely $\sigma_s\circ\kappa=\kappa$; for the analogous $\kappa$ over $k_1$, $\sigma_s\circ\kappa=\kappa\circ\tau_s$; and for the analogous $\kappa$ over $k_2$, $\sigma_s\circ\kappa=\kappa\circ\tau'_s$.
--
--   This is the geometric half of a Schlessinger-style gluing step: over a base presenting a triple fibre product $B\times_{B_1}B\times_{B_1}B$, automorphisms of the overlaps of a deformation over $B$ are amalgamated into a single automorphism of the overlaps of the base-changed deformation over $B'$, with prescribed restrictions along the three sections. It is used by [`GoodReductionJacobian.BareDeformation.exists_overlap_isos_comap_of_sections`](thm.html#GoodReductionJacobian.BareDeformation.exists_overlap_isos_comap_of_sections), where the cocycle conditions needed for gluing the overlap automorphisms are then imposed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_overlap_isos_comap_slice.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_overlap_isos_comap_slice
    (B' B B₁ : Type) [CommRing B'] [CommRing B] [CommRing B₁] [Algebra B' B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁))
    (δ : B →+* B') (hδ : (algebraMap B' B₁).comp δ = algebraMap B B₁)
    (p₀ p₁ p₂ : B' →+* B) (hp₀δ : p₀.comp δ = RingHom.id B) (hp₁δ : p₁.comp δ = RingHom.id B) (hp₂δ : p₂.comp δ = RingHom.id B)
    (hp₀ : (algebraMap B B₁).comp p₀ = algebraMap B' B₁) (hp₁ : (algebraMap B B₁).comp p₁ = algebraMap B' B₁)
    (hp₂ : (algebraMap B B₁).comp p₂ = algebraMap B' B₁)
    (hinj : ∀ x y : B', p₀ x = p₀ y → p₁ x = p₁ y → p₂ x = p₂ y → x = y)
    (hsurj : ∀ b₀ b₁ b₂ : B, algebraMap B B₁ b₀ = algebraMap B B₁ b₁ → algebraMap B B₁ b₁ = algebraMap B B₁ b₂ →
      ∃ x : B', p₀ x = b₀ ∧ p₁ x = b₁ ∧ p₂ x = b₂)
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f] (D₀' : BareDeformation f₁ L₁ B')
    (h' : D₀'.A ⟶ D₀.A) [IsAffineHom h'] (hc' : IsPullback h' D₀'.f D₀.f (Spec.map (CommRingCat.ofHom δ)))
    (hg' : D₀'.g ≫ h' = D₀.g)
    (k₀ k₁ k₂ : D₀.A ⟶ D₀'.A) (hk₀ : k₀ ≫ h' = 𝟙 D₀.A) (hk₁ : k₁ ≫ h' = 𝟙 D₀.A) (hk₂ : k₂ ≫ h' = 𝟙 D₀.A)
    (hk₀f : k₀ ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom p₀)) (hk₁f : k₁ ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom p₁))
    (hk₂f : k₂ ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom p₂))
    (𝒰 : D₀.A.OrderedAffineCover)
    (τ τ' : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (hτB : ∀ s : 𝒰.Idx 1, (τ s).hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f)
    (hτg : ∀ s : 𝒰.Idx 1, (D₀.g ∣_ 𝒰.inter s) ≫ (τ s).hom = D₀.g ∣_ 𝒰.inter s)
    (hτ'B : ∀ s : 𝒰.Idx 1, (τ' s).hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f)
    (hτ'g : ∀ s : 𝒰.Idx 1, (D₀.g ∣_ 𝒰.inter s) ≫ (τ' s).hom = D₀.g ∣_ 𝒰.inter s) :
    ∃ σ : ∀ s : (𝒰.comap h').Idx 1, ((↑((𝒰.comap h').inter s) : Scheme.{0}) ≅ ↑((𝒰.comap h').inter s)),
      (∀ s : (𝒰.comap h').Idx 1, (σ s).hom ≫ ((𝒰.comap h').inter s).ι ≫ D₀'.f = ((𝒰.comap h').inter s).ι ≫ D₀'.f) ∧
      (∀ s : (𝒰.comap h').Idx 1, (D₀'.g ∣_ (𝒰.comap h').inter s) ≫ (σ s).hom = D₀'.g ∣_ (𝒰.comap h').inter s) ∧
      (∀ (s : 𝒰.Idx 1) (κ : (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter s)),
        κ ≫ ((𝒰.comap h').inter s).ι = (𝒰.inter s).ι ≫ k₀ → κ ≫ (σ s).hom = κ) ∧
      (∀ (s : 𝒰.Idx 1) (κ : (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter s)),
        κ ≫ ((𝒰.comap h').inter s).ι = (𝒰.inter s).ι ≫ k₁ → (τ s).hom ≫ κ = κ ≫ (σ s).hom) ∧
      (∀ (s : 𝒰.Idx 1) (κ : (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter s)),
        κ ≫ ((𝒰.comap h').inter s).ι = (𝒰.inter s).ι ≫ k₂ → (τ' s).hom ≫ κ = κ ≫ (σ s).hom) := by sorry
