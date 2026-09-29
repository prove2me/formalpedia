-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_overlap_isos_comap_of_sections
-- name    : GoodReductionJacobian.BareDeformation.exists_overlap_isos_comap_of_sections
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/f34053ce-5623-5472-844f-0c40c22188c6
-- title:
--   Overlap automorphisms over a triple fibre product base
-- statement:
--   Let $B'$, $B$, $B_1$ be commutative rings with $B_1$ an algebra over both $B'$ and $B$, let $\mathrm{algebraMap}\,B\,B_1$ be surjective, and let $\delta : B \to B'$ satisfy $\mathrm{algebraMap}\,B'\,B_1 \circ \delta = \mathrm{algebraMap}\,B\,B_1$. Let $p_0,p_1,p_2 : B' \to B$ be ring maps, each a retraction of $\delta$ ($p_i \circ \delta = \mathrm{id}_B$) and each compatible with the maps to $B_1$, such that $(p_0,p_1,p_2)$ is jointly injective and every triple $(b_0,b_1,b_2)$ with equal images in $B_1$ is realised; thus $B'$ is the triple fibre product of $B$ over $B_1$. Let $f_1 : A_1 \to \operatorname{Spec} B_1$ carry a relative group law $L_1$, let $D_0$ be a bare deformation of $(f_1,L_1)$ over $B$ with $D_0.f$ separated, and $D_0'$ one over $B'$. Let $h' : D_0'.A \to D_0.A$ be an affine morphism making $D_0'.f$, $D_0.f$ cartesian over $\operatorname{Spec}\delta$ with $D_0'.g$ followed by $h'$ equal to $D_0.g$, and let $k_0,k_1,k_2 : D_0.A \to D_0'.A$ be sections of $h'$ lying over $\operatorname{Spec} p_0, \operatorname{Spec} p_1, \operatorname{Spec} p_2$ respectively. Let $\mathcal U$ be a finite ordered affine cover of $D_0.A$ (a finite linearly ordered family of affine opens with supremum $\top$), and let $\tau,\tau'$ assign to each pairwise index $s$ an automorphism of the overlap $\mathcal U.\mathrm{inter}\,s$ which commutes with the structure map to $\operatorname{Spec} B$ and fixes the restriction of $D_0.g$; assume for each triple index $r$ that there are endomorphisms $\rho_0,\rho_1,\rho_2$ of $\mathcal U.\mathrm{inter}\,r$ intertwining the inclusions into the three faces with the corresponding $\tau$ (respectively $\tau'$) and satisfying $\rho_1 = \rho_2$ followed by $\rho_0$. Then there is a family $\sigma$ of automorphisms of the overlaps of the preimage cover $\mathcal U.\mathrm{comap}\,h'$ on $D_0'.A$ which commute with the structure map to $\operatorname{Spec} B'$, fix the restrictions of $D_0'.g$, satisfy the same triple-overlap cocycle condition, and whose restrictions along any morphism $\kappa$ from $\mathcal U.\mathrm{inter}\,s$ into the corresponding preimage overlap that is compatible with $k_0$, $k_1$, $k_2$ respectively equal $\mathrm{id}$, $\tau_s$ and $\tau'_s$: namely $\kappa \sigma_s = \kappa$, $\kappa \tau_s = \sigma_s \kappa$ and $\kappa \tau'_s = \sigma_s \kappa$ in diagrammatic order.
--
--   This is the gluing-datum step in the deformation theory of the abelian scheme attached to the relevant moduli problem: it produces, over a base which is a triple fibre product, a single family of overlap automorphisms whose three slices are prescribed, together with the cocycle condition needed to reglue. It is used in the comparison of regluings with tangent coordinates, in the analysis of shifts by additive data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_overlap_isos_comap_of_sections.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_overlap_isos_comap_of_sections
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
    (hτ'g : ∀ s : 𝒰.Idx 1, (D₀.g ∣_ 𝒰.inter s) ≫ (τ' s).hom = D₀.g ∣_ 𝒰.inter s)
    (hcocτ : ∀ r : 𝒰.Idx 2, ∃ ρ : Fin 3 → ((↑(𝒰.inter r) : Scheme.{0}) ⟶ ↑(𝒰.inter r)),
        (∀ j : Fin 3, ρ j ≫ D₀.A.homOfLE (𝒰.inter_le_inter_face r j)
            = D₀.A.homOfLE (𝒰.inter_le_inter_face r j) ≫ (τ (𝒰.face r j)).hom) ∧
        ρ 1 = ρ 2 ≫ ρ 0)
    (hcocτ' : ∀ r : 𝒰.Idx 2, ∃ ρ : Fin 3 → ((↑(𝒰.inter r) : Scheme.{0}) ⟶ ↑(𝒰.inter r)),
        (∀ j : Fin 3, ρ j ≫ D₀.A.homOfLE (𝒰.inter_le_inter_face r j)
            = D₀.A.homOfLE (𝒰.inter_le_inter_face r j) ≫ (τ' (𝒰.face r j)).hom) ∧
        ρ 1 = ρ 2 ≫ ρ 0) :
    ∃ σ : ∀ s : (𝒰.comap h').Idx 1, ((↑((𝒰.comap h').inter s) : Scheme.{0}) ≅ ↑((𝒰.comap h').inter s)),
      (∀ s : (𝒰.comap h').Idx 1, (σ s).hom ≫ ((𝒰.comap h').inter s).ι ≫ D₀'.f = ((𝒰.comap h').inter s).ι ≫ D₀'.f) ∧
      (∀ s : (𝒰.comap h').Idx 1, (D₀'.g ∣_ (𝒰.comap h').inter s) ≫ (σ s).hom = D₀'.g ∣_ (𝒰.comap h').inter s) ∧
      (∀ r : (𝒰.comap h').Idx 2, ∃ ρ : Fin 3 → ((↑((𝒰.comap h').inter r) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter r)),
        (∀ j : Fin 3, ρ j ≫ D₀'.A.homOfLE ((𝒰.comap h').inter_le_inter_face r j)
            = D₀'.A.homOfLE ((𝒰.comap h').inter_le_inter_face r j) ≫ (σ ((𝒰.comap h').face r j)).hom) ∧
        ρ 1 = ρ 2 ≫ ρ 0) ∧
      (∀ (s : 𝒰.Idx 1) (κ : (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter s)),
        κ ≫ ((𝒰.comap h').inter s).ι = (𝒰.inter s).ι ≫ k₀ → κ ≫ (σ s).hom = κ) ∧
      (∀ (s : 𝒰.Idx 1) (κ : (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter s)),
        κ ≫ ((𝒰.comap h').inter s).ι = (𝒰.inter s).ι ≫ k₁ → (τ s).hom ≫ κ = κ ≫ (σ s).hom) ∧
      (∀ (s : 𝒰.Idx 1) (κ : (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter s)),
        κ ≫ ((𝒰.comap h').inter s).ι = (𝒰.inter s).ι ≫ k₂ → (τ' s).hom ≫ κ = κ ≫ (σ s).hom) := by sorry
