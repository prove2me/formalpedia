-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_chartIso_comp_eq_of_isRegluingBy_of_isIso
-- name    : GoodReductionJacobian.BareDeformation.exists_chartIso_comp_eq_of_isRegluingBy_of_isIso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/553cd0cf-e401-5a03-b1ad-7fffc9ee6f0d
-- title:
--   Isomorphic regluings give compatible chart automorphisms
-- statement:
--   Let $B \to B_1$ be a surjective ring homomorphism with nilpotent kernel, let $f_1 : A_1 \to \operatorname{Spec} B_1$ be a scheme over $B_1$ and $L_1$ a relative group law on $f_1$. Let $D_0, D, D'$ be bare deformations of $(f_1, L_1)$ to $B$: each carries a scheme $A$ with structure map $f$ to $\operatorname{Spec} B$, a commutative relative group law, an abelian-scheme property bundle, and a morphism $g : A_1 \to A$ whose square over $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ is cartesian and which is compatible with the group laws. Let $\mathcal{U}$ be an ordered affine cover of $D_0.A$ (a finite linearly ordered index set $\iota$, affine opens $U_i$ with $\bigsqcup_i U_i = \top$), write $U_s = U_{s(0)} \sqcap U_{s(1)}$ for $s$ a strictly monotone pair, and let $\tau_s, \tau'_s$ be self-isomorphisms of the schemes $U_s$. Assume `IsRegluingBy` holds for $(\mathcal{U}, \tau, D)$ and for $(\mathcal{U}, \tau', D')$, i.e. each $\tau_s$ (resp. $\tau'_s$) commutes with $U_s \hookrightarrow D_0.A \to \operatorname{Spec} B$ and fixes the restriction $D_0.g \mid_{U_s}$, and there are open immersions $\iota_i : U_i \to D.A$ (resp. $\iota'_i : U_i \to D'.A$) over $\operatorname{Spec} B$, jointly surjective on points, compatible with $D_0.g$ and $D.g$ (resp. $D'.g$), and satisfying the regluing identity $U_s \to U_{s(0)} \xrightarrow{\iota_{s(0)}} D.A \;=\; \tau_s$ followed by $U_s \to U_{s(1)} \xrightarrow{\iota_{s(1)}} D.A$. Assume finally that $D$ and $D'$ are isomorphic as bare deformations: there is an isomorphism $e : D.A \cong D'.A$ with $e$ followed by $D'.f$ equal to $D.f$ and $D.g$ followed by $e$ equal to $D'.g$. Then there exist self-isomorphisms $\alpha_i$ of each $U_i$ and, for each strictly monotone pair $s$ and each $j \in \{0,1\}$, self-isomorphisms $\alpha^r_{s,j}$ of $U_s$, such that each $\alpha_i$ commutes with $U_i \hookrightarrow D_0.A \to \operatorname{Spec} B$, each $\alpha_i$ fixes $D_0.g \mid_{U_i}$, each $\alpha^r_{s,j}$ is compatible with $\alpha_{s(j)}$ along the inclusion $U_s \to U_{s(j)}$, and $\alpha^r_{s,0}$ followed by $\tau'_s$ equals $\tau_s$ followed by $\alpha^r_{s,1}$.
--
--   This is the converse direction of the gluing description of deformations: an isomorphism between two regluings of the same bare deformation $D_0$ along a fixed ordered affine cover is induced by automorphisms of the charts and of their overlaps, intertwining the two systems of transition automorphisms. It is used in the comparison of tangent-space coordinates for bare deformations, in the statements producing a difference cocycle from an isomorphism of deformations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_chartIso_comp_eq_of_isRegluingBy_of_isIso.lean

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

theorem GoodReductionJacobian.BareDeformation.exists_chartIso_comp_eq_of_isRegluingBy_of_isIso
    {B B₁ : Type} [CommRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (D₀ D D' : BareDeformation f₁ L₁ B) (𝒰 : D₀.A.OrderedAffineCover)
    (τ τ' : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (hD : D₀.IsRegluingBy 𝒰 τ D) (hD' : D₀.IsRegluingBy 𝒰 τ' D')
    (hiso : D.IsIso D') :
    ∃ (α : ∀ i : 𝒰.ι, ((↑(𝒰.U i) : Scheme.{0}) ≅ ↑(𝒰.U i)))
      (αr : ∀ (s : 𝒰.Idx 1) (_ : Fin 2), ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s))),
      (∀ i : 𝒰.ι, (α i).hom ≫ (𝒰.U i).ι ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f) ∧
      (∀ i : 𝒰.ι, (D₀.g ∣_ 𝒰.U i) ≫ (α i).hom = D₀.g ∣_ 𝒰.U i) ∧
      (∀ (s : 𝒰.Idx 1) (j : Fin 2),
        (αr s j).hom ≫ D₀.A.homOfLE (𝒰.inter_le s j) = D₀.A.homOfLE (𝒰.inter_le s j) ≫ (α (s.1 j)).hom) ∧
      (∀ s : 𝒰.Idx 1, (αr s 0).hom ≫ (τ' s).hom = (τ s).hom ≫ (αr s 1).hom) := by sorry
