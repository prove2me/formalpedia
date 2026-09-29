-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_endo_comap_inter_of_slices
-- name    : GoodReductionJacobian.BareDeformation.exists_endo_comap_inter_of_slices
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/57938014-ad75-58c9-8fc3-253fbbf5231a
-- title:
--   Slice-prescribed endomorphism of a pulled-back overlap
-- statement:
--   Let $B'$, $B$, $B_1$ be commutative rings with $B_1$ an algebra over both $B'$ and $B$, the map $B \to B_1$ surjective, let $\delta : B \to B'$ be a ring homomorphism lying over $B_1$ (i.e. $\delta$ followed by $B' \to B_1$ is $B \to B_1$), and let $p_0,p_1,p_2 : B' \to B$ each be a retraction of $\delta$ and each compatible with the maps to $B_1$; assume the $p_i$ are jointly injective and that every triple $(b_0,b_1,b_2)$ in $B$ with equal images in $B_1$ is $(p_0x,p_1x,p_2x)$ for some $x \in B'$. Let $f_1 : A_1 \to \operatorname{Spec} B_1$ carry a relative group law $L_1$, and let $D_0$ over $B$ and $D_0'$ over $B'$ be bare deformations of $(f_1,L_1)$, that is schemes with structure morphism, commutative relative group law, abelian-scheme property bundle, and a comparison morphism $g$ from $A_1$ cartesian over the respective base change and compatible with the group laws; assume $D_0.f$ separated. Let $h' : D_0'.A \to D_0.A$ be an affine morphism making a pullback square of $D_0'.f$ over $D_0.f$ along $\operatorname{Spec}\delta$, with $D_0'.g$ followed by $h'$ equal to $D_0.g$, and let $k_0,k_1,k_2$ be sections of $h'$ lying over $\operatorname{Spec} p_0,\operatorname{Spec} p_1,\operatorname{Spec} p_2$. Let $\mathcal U$ be a finite ordered affine cover of $D_0.A$, let $t$ be a strictly monotone $(n+1)$-tuple of indices, and let $U_t$ be the corresponding intersection of members of $\mathcal U$. Given endomorphisms $\alpha,\alpha'$ of $U_t$ over $\operatorname{Spec} B$ each fixing the restriction of $D_0.g$ to $U_t$, the assertion is that there is an endomorphism $\sigma$ of the corresponding intersection $U_t'$ for the cover $\mathcal U$ pulled back along $h'$ (the intersection of the preimages $h'^{-1}(\mathcal U.U(t_j))$), such that $\sigma$ is a morphism over $\operatorname{Spec} B'$, it fixes the restriction of $D_0'.g$ to $U_t'$, and for every $\kappa : U_t \to U_t'$ whose composite with the inclusion of $U_t'$ equals the inclusion of $U_t$ followed by $k_0$ (respectively $k_1$, $k_2$) one has $\kappa$ followed by $\sigma$ equal to $\kappa$ (respectively equal to $\alpha$ followed by $\kappa$, and to $\alpha'$ followed by $\kappa$).
--
--   The hypotheses on $p_0,p_1,p_2$ identify $B'$ with the triple fibre product $B \times_{B_1} B \times_{B_1} B$, and the statement is the local, Schlessinger-style additivity step for deformations of the given abelian-scheme data: two endomorphisms of an overlap that are trivial modulo the kernel of $B \to B_1$ are combined, together with the identity, into a single endomorphism over $B'$ whose three slices recover them. It is used in the construction of the cocycle of overlap isomorphisms for the pulled-back cover, in [`GoodReductionJacobian.BareDeformation.overlap_isos_comap_cocycle_of_slice`](thm.html#GoodReductionJacobian.BareDeformation.overlap_isos_comap_cocycle_of_slice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_endo_comap_inter_of_slices.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_endo_comap_inter_of_slices
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
    {n : ℕ} (t : 𝒰.Idx n)
    (α α' : (↑(𝒰.inter t) : Scheme.{0}) ⟶ ↑(𝒰.inter t))
    (hαB : α ≫ (𝒰.inter t).ι ≫ D₀.f = (𝒰.inter t).ι ≫ D₀.f) (hαg : (D₀.g ∣_ 𝒰.inter t) ≫ α = D₀.g ∣_ 𝒰.inter t)
    (hα'B : α' ≫ (𝒰.inter t).ι ≫ D₀.f = (𝒰.inter t).ι ≫ D₀.f) (hα'g : (D₀.g ∣_ 𝒰.inter t) ≫ α' = D₀.g ∣_ 𝒰.inter t) :
    ∃ σ : (↑((𝒰.comap h').inter t) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter t),
      σ ≫ ((𝒰.comap h').inter t).ι ≫ D₀'.f = ((𝒰.comap h').inter t).ι ≫ D₀'.f ∧
      (D₀'.g ∣_ (𝒰.comap h').inter t) ≫ σ = D₀'.g ∣_ (𝒰.comap h').inter t ∧
      (∀ κ : (↑(𝒰.inter t) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter t),
        κ ≫ ((𝒰.comap h').inter t).ι = (𝒰.inter t).ι ≫ k₀ → κ ≫ σ = κ) ∧
      (∀ κ : (↑(𝒰.inter t) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter t),
        κ ≫ ((𝒰.comap h').inter t).ι = (𝒰.inter t).ι ≫ k₁ → α ≫ κ = κ ≫ σ) ∧
      (∀ κ : (↑(𝒰.inter t) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter t),
        κ ≫ ((𝒰.comap h').inter t).ι = (𝒰.inter t).ι ≫ k₂ → α' ≫ κ = κ ≫ σ) := by sorry
