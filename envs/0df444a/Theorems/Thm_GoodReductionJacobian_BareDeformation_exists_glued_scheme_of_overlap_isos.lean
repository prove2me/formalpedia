-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_glued_scheme_of_overlap_isos
-- name    : GoodReductionJacobian.BareDeformation.exists_glued_scheme_of_overlap_isos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/44055bca-d1bc-50cc-9263-31368e57468d
-- title:
--   Gluing deformation charts along overlap automorphisms
-- statement:
--   Let $B$ and $B_1$ be commutative rings with $B_1$ a $B$-algebra such that the structure map $B \to B_1$ is surjective with nilpotent kernel, let $f_1 \colon A_1 \to \operatorname{Spec} B_1$ be a scheme with a relative group law $L_1$, and let $D_0$ be a bare deformation of $(f_1,L_1)$ to $B$: a scheme $D_0.A$ with a structure morphism $D_0.f \colon D_0.A \to \operatorname{Spec} B$, a commutative relative group law, an abelian-scheme property bundle, and a morphism $D_0.g \colon A_1 \to D_0.A$ making the square over $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ cartesian and compatible with the two group laws; assume $D_0.f$ separated. Let $\mathcal U$ be an ordered affine cover of $D_0.A$, i.e. a finite linearly ordered index set $\iota$ together with affine opens $U_i$ whose supremum is $\top$. For $s$ a strictly increasing pair of indices write $U_s = \bigcap_j U_{s(j)}$, and suppose given an isomorphism $\tau_s$ of $U_s$ with itself such that $\tau_s$ followed by the inclusion of $U_s$ and then $D_0.f$ equals the inclusion followed by $D_0.f$, and such that the restriction $D_0.g \mid_{U_s}$ followed by $\tau_s$ equals $D_0.g \mid_{U_s}$. Suppose further that for every strictly increasing triple $r$ there are endomorphisms $\rho_0,\rho_1,\rho_2$ of $U_r$ with $\rho_j$ followed by the inclusion $U_r \subseteq U_{\partial_j r}$ equal to that inclusion followed by $\tau_{\partial_j r}$, and $\rho_1 = \rho_0 \circ \rho_2$. Then there exist a scheme $X$, a morphism $f_X \colon X \to \operatorname{Spec} B$, morphisms $\iota_i \colon U_i \to X$ and a morphism $g_X \colon A_1 \to X$ such that: each $\iota_i$ is an open immersion; $\iota_i$ followed by $f_X$ equals the inclusion of $U_i$ followed by $D_0.f$; every point of $X$ lies in the image of some $\iota_i$; for each $i$ the restriction $D_0.g \mid_{U_i}$ followed by $\iota_i$ equals the inclusion of $D_0.g^{-1}(U_i)$ followed by $g_X$; for each pair $s$ the inclusion $U_s \subseteq U_{s(0)}$ followed by $\iota_{s(0)}$ equals $\tau_s$ followed by the inclusion $U_s \subseteq U_{s(1)}$ and then $\iota_{s(1)}$; the square formed by $g_X$, $f_1$, $f_X$ and $\operatorname{Spec}$ of $B \to B_1$ is cartesian; and $f_X$ is smooth.
--
--   This is the gluing step in the re-gluing construction for deformations of abelian schemes: a $1$-cocycle of automorphisms of the pairwise overlaps of an ordered affine cover, each trivial over the base and trivial on the special fibre, is used to reassemble the charts into a new smooth scheme over $\operatorname{Spec} B$ whose base change to $B_1$ is again $f_1$. The five gluing clauses are exactly the data required of a re-glued deformation, and the result is used in the construction of re-gluings realising prescribed tangent coordinates and in the additivity of the associated shift.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_glued_scheme_of_overlap_isos.lean

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
  CerednikDrinfeld.SpecialFormal IsLocalRing Scheme.TwoAffineOpenCover
open scoped Quaternion TensorProduct NumberField

theorem GoodReductionJacobian.BareDeformation.exists_glued_scheme_of_overlap_isos
    (B B₁ : Type) [CommRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)
    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f]
    (𝒰 : D₀.A.OrderedAffineCover)
    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (hτB : ∀ s : 𝒰.Idx 1, (τ s).hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f)
    (hτg : ∀ s : 𝒰.Idx 1, (D₀.g ∣_ 𝒰.inter s) ≫ (τ s).hom = D₀.g ∣_ 𝒰.inter s)
    (hcoc : ∀ r : 𝒰.Idx 2, ∃ ρ : Fin 3 → ((↑(𝒰.inter r) : Scheme.{0}) ⟶ ↑(𝒰.inter r)),
        (∀ j : Fin 3, ρ j ≫ D₀.A.homOfLE (𝒰.inter_le_inter_face r j)
            = D₀.A.homOfLE (𝒰.inter_le_inter_face r j) ≫ (τ (𝒰.face r j)).hom) ∧
        ρ 1 = ρ 2 ≫ ρ 0) :
    ∃ (X : Scheme.{0}) (fX : X ⟶ Spec (CommRingCat.of B)) (ιU : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ X)
      (gX : A₁ ⟶ X),
      ((∀ i, IsOpenImmersion (ιU i)) ∧
      (∀ i, ιU i ≫ fX = (𝒰.U i).ι ≫ D₀.f) ∧
      (∀ x : X, ∃ (i : 𝒰.ι) (y : ↑(𝒰.U i)), (ιU i).base y = x) ∧
      (∀ i, (D₀.g ∣_ 𝒰.U i) ≫ ιU i = (D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ gX) ∧
      (∀ s : 𝒰.Idx 1,
        D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ιU (s.1 0) = (τ s).hom ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ιU (s.1 1))) ∧
      IsPullback gX f₁ fX (Spec.map (CommRingCat.ofHom (algebraMap B B₁))) ∧
      Smooth fX := by sorry
