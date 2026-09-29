-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_overlap_isos_comap_cocycle_of_slice
-- name    : GoodReductionJacobian.BareDeformation.overlap_isos_comap_cocycle_of_slice
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/29fd3a3d-d5dc-5841-9fff-a2a8d1a2f54b
-- title:
--   Cocycle identity descends to the base-changed overlap automorphisms
-- statement:
--   Let $B'$, $B$, $B_1$ be commutative rings with $B_1$ an algebra over both $B'$ and $B$, the structure map $B \to B_1$ surjective, and let $\delta : B \to B'$ be a ring homomorphism with $B' \to B_1$ composed after $\delta$ equal to $B \to B_1$. Let $p_0,p_1,p_2 : B' \to B$ each satisfy $p_i \circ \delta = \mathrm{id}_B$ and be compatible with the maps to $B_1$; assume the triple $(p_0,p_1,p_2)$ is jointly injective, and that every triple $b_0,b_1,b_2 \in B$ with equal images in $B_1$ is of the form $(p_0x,p_1x,p_2x)$ for some $x \in B'$. Let $f_1 : A_1 \to \operatorname{Spec} B_1$ carry a relative group law $L_1$, let $D_0$ be a bare deformation of $(f_1,L_1)$ over $B$ with $D_0.f$ separated, $D_0'$ one over $B'$, and let $h' : D_0'.A \to D_0.A$ be an affine morphism making $D_0'.f$ the base change of $D_0.f$ along $\operatorname{Spec}\delta$, with $D_0'.g$ followed by $h'$ equal to $D_0.g$. Let $k_0,k_1,k_2 : D_0.A \to D_0'.A$ be sections of $h'$ lying over $\operatorname{Spec} p_0,\operatorname{Spec} p_1,\operatorname{Spec} p_2$. Fix an ordered affine cover $\mathcal{U}$ of $D_0.A$ (a finite linearly ordered family of affine opens covering $D_0.A$), whose double overlaps are the intersections indexed by strictly monotone $s : \mathrm{Fin}\,2 \to \mathcal{U}.\iota$ and triple overlaps by strictly monotone $r : \mathrm{Fin}\,3 \to \mathcal{U}.\iota$. Let $\tau_s,\tau'_s$ be automorphisms of the double overlaps commuting with the inclusion followed by $D_0.f$ and fixing the restriction of $D_0.g$, and assume both families satisfy the cocycle condition: for each triple index $r$ there are endomorphisms $\rho_0,\rho_1,\rho_2$ of the triple overlap compatible, via the inclusions of the triple overlap into the three faces, with $\tau$ (resp. $\tau'$) at those faces, and with $\rho_1 = \rho_0 \circ \rho_2$. Finally let $\sigma$ be automorphisms of the double overlaps of the preimage cover $\mathcal{U}.\mathrm{comap}\,h'$ (the opens $h'^{-1}U_i$), commuting with the inclusion followed by $D_0'.f$, and whose three slices are prescribed: every $\kappa$ from the overlap in $D_0.A$ to the corresponding overlap in $D_0'.A$ lying over $k_0$ satisfies $\kappa$ followed by $\sigma_s$ equals $\kappa$, while for $\kappa$ lying over $k_1$ (resp. $k_2$) one has $\tau_s$ followed by $\kappa$ equal to $\kappa$ followed by $\sigma_s$ (resp. with $\tau'_s$). Then $\sigma$ satisfies the same cocycle condition on the triple overlaps of $\mathcal{U}.\mathrm{comap}\,h'$: for each triple index $r$ there exist endomorphisms $\rho_0,\rho_1,\rho_2$ of that triple overlap, compatible with $\sigma$ at the three faces via the face inclusions, and with $\rho_1 = \rho_0 \circ \rho_2$.
--
--   This is the cocycle step of a regluing argument: a family of automorphisms of the overlaps of the base-changed abelian scheme, determined by its three slices along the sections $k_0,k_1,k_2$, inherits the triple-overlap cocycle identity from the two given families on the base. It is used in the construction of the overlap isomorphisms for the cover obtained by pulling back along $h'$, in the deformation-theoretic input to the good-reduction analysis of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_overlap_isos_comap_cocycle_of_slice.lean

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

theorem GoodReductionJacobian.BareDeformation.overlap_isos_comap_cocycle_of_slice
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
        ρ 1 = ρ 2 ≫ ρ 0)
    (σ : ∀ s : (𝒰.comap h').Idx 1, ((↑((𝒰.comap h').inter s) : Scheme.{0}) ≅ ↑((𝒰.comap h').inter s)))
    (hσB : (∀ s : (𝒰.comap h').Idx 1, (σ s).hom ≫ ((𝒰.comap h').inter s).ι ≫ D₀'.f = ((𝒰.comap h').inter s).ι ≫ D₀'.f))
    (hσ₀ : (∀ (s : 𝒰.Idx 1) (κ : (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter s)),
        κ ≫ ((𝒰.comap h').inter s).ι = (𝒰.inter s).ι ≫ k₀ → κ ≫ (σ s).hom = κ))
    (hσ₁ : (∀ (s : 𝒰.Idx 1) (κ : (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter s)),
        κ ≫ ((𝒰.comap h').inter s).ι = (𝒰.inter s).ι ≫ k₁ → (τ s).hom ≫ κ = κ ≫ (σ s).hom))
    (hσ₂ : (∀ (s : 𝒰.Idx 1) (κ : (↑(𝒰.inter s) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter s)),
        κ ≫ ((𝒰.comap h').inter s).ι = (𝒰.inter s).ι ≫ k₂ → (τ' s).hom ≫ κ = κ ≫ (σ s).hom)) :
    (∀ r : (𝒰.comap h').Idx 2, ∃ ρ : Fin 3 → ((↑((𝒰.comap h').inter r) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter r)),
        (∀ j : Fin 3, ρ j ≫ D₀'.A.homOfLE ((𝒰.comap h').inter_le_inter_face r j)
            = D₀'.A.homOfLE ((𝒰.comap h').inter_le_inter_face r j) ≫ (σ ((𝒰.comap h').face r j)).hom) ∧
        ρ 1 = ρ 2 ≫ ρ 0) := by sorry
