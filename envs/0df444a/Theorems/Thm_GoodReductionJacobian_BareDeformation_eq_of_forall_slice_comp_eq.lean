-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_eq_of_forall_slice_comp_eq
-- name    : GoodReductionJacobian.BareDeformation.eq_of_forall_slice_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/44f6bd54-af8d-57b5-813e-e1329b843133
-- title:
--   Three slices jointly determine morphisms of pulled-back overlaps
-- statement:
--   Let $B'$, $B$, $B_1$ be commutative rings with $B_1$ an algebra over both $B'$ and $B$, such that $B\to B_1$ is surjective, and let $\delta : B \to B'$ be a ring homomorphism with $B\to B'\to B_1$ equal to $B\to B_1$. Let $p_0,p_1,p_2 : B' \to B$ be ring homomorphisms, each a retraction of $\delta$ ($p_i\circ\delta = \mathrm{id}_B$) and each compatible with the maps to $B_1$ ($B'\to B_1$ factors as $p_i$ followed by $B\to B_1$); assume $(p_0,p_1,p_2)$ is jointly injective, and that any triple $b_0,b_1,b_2\in B$ with equal images in $B_1$ is of the form $(p_0x,p_1x,p_2x)$ for some $x\in B'$ — so $B'$ is a fibre product $B\times_{B_1}B\times_{B_1}B$. Let $f_1 : A_1 \to \operatorname{Spec} B_1$ carry a relative group law $L_1$ (functorial multiplication, unit and inverse on $T$-points over $\operatorname{Spec}B_1$, with the group axioms and naturality). Let $D_0$ be a bare deformation of $(f_1,L_1)$ over $B$, that is, a scheme $D_0.A$ with structure morphism $D_0.f$ to $\operatorname{Spec}B$, a commutative relative group law, an abelian-scheme property bundle, and a morphism $D_0.g : A_1 \to D_0.A$ making the square over $\operatorname{Spec}(B\to B_1)$ cartesian and compatible with the group laws; assume $D_0.f$ separated. Let $D_0'$ be a bare deformation over $B'$, and $h' : D_0'.A \to D_0.A$ an affine morphism making the square with $D_0'.f$, $D_0.f$ and $\operatorname{Spec}\delta$ cartesian, with $D_0'.g$ followed by $h'$ equal to $D_0.g$. Let $k_0,k_1,k_2 : D_0.A \to D_0'.A$ satisfy $k_i$ followed by $h'$ equal to the identity and $k_i$ followed by $D_0'.f$ equal to $D_0.f$ followed by $\operatorname{Spec}p_i$. Let $\mathcal{U}$ be an ordered affine cover of $D_0.A$ (a finite linearly ordered family of affine opens with supremum $\top$), and let $t$, $t'$ be strictly increasing tuples of indices of lengths $n+1$, $n'+1$, with $\mathcal{U}.\mathrm{inter}$ the corresponding intersections of the opens, and $(\mathcal{U}.\mathrm{comap}\,h')$ the cover of $D_0'.A$ by the $h'$-preimages of the $\mathcal{U}.U_i$. Then for two morphisms $a,b$ from the open subscheme $(\mathcal{U}.\mathrm{comap}\,h').\mathrm{inter}\,t$ to $(\mathcal{U}.\mathrm{comap}\,h').\mathrm{inter}\,t'$: if for each $i\in\{0,1,2\}$ and each morphism $\kappa$ from $\mathcal{U}.\mathrm{inter}\,t$ to $(\mathcal{U}.\mathrm{comap}\,h').\mathrm{inter}\,t$ whose composite with the open immersion into $D_0'.A$ equals the open immersion of $\mathcal{U}.\mathrm{inter}\,t$ followed by $k_i$, one has $\kappa$ followed by $a$ equal to $\kappa$ followed by $b$, then $a = b$.
--
--   This is the uniqueness half of the slice formalism for deformations over a triple fibre product $B' = B\times_{B_1}B\times_{B_1}B$: the three sections $k_0,k_1,k_2$ are jointly epimorphic on each pulled-back overlap, so a morphism of such overlaps is determined by its restrictions along them. It is the ingredient that makes slice-glued data unambiguous, and is used in [`GoodReductionJacobian.BareDeformation.overlap_isos_comap_cocycle_of_slice`](thm.html#GoodReductionJacobian.BareDeformation.overlap_isos_comap_cocycle_of_slice) to verify the cocycle condition for the overlap isomorphisms. The proof cites the affineness and pushout description of preimages of affine opens under a cartesian affine morphism, the ring-level description of the sections $k_i$ on sections over such opens, and a joint-injectivity statement for the three induced maps out of a flat pushout.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_eq_of_forall_slice_comp_eq.lean

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

theorem GoodReductionJacobian.BareDeformation.eq_of_forall_slice_comp_eq
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
    {n n' : ℕ} (t : 𝒰.Idx n) (t' : 𝒰.Idx n')
    (a b : (↑((𝒰.comap h').inter t) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter t'))
    (h₀ : ∀ κ : (↑(𝒰.inter t) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter t), κ ≫ ((𝒰.comap h').inter t).ι = (𝒰.inter t).ι ≫ k₀ → κ ≫ a = κ ≫ b)
    (h₁ : ∀ κ : (↑(𝒰.inter t) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter t), κ ≫ ((𝒰.comap h').inter t).ι = (𝒰.inter t).ι ≫ k₁ → κ ≫ a = κ ≫ b)
    (h₂ : ∀ κ : (↑(𝒰.inter t) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter t), κ ≫ ((𝒰.comap h').inter t).ι = (𝒰.inter t).ι ≫ k₂ → κ ≫ a = κ ≫ b) :
    a = b := by sorry
