-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_of_bareDeformation_bare
-- name    : GoodReductionJacobian.BareDeformation.exists_isRegluingBy_of_bareDeformation_bare
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/64eb78d9-6f8a-5796-99e8-fdbe5dfe18cd
-- title:
--   Every bare deformation re-glues a fixed one on an affine cover
-- statement:
--   Let $B$ be an Artinian local commutative ring and $B_1$ a commutative $B$-algebra such that the structure map $B \to B_1$ is surjective with nilpotent kernel. Let $f_1 : A_1 \to \operatorname{Spec} B_1$ be a morphism of schemes and $L_1$ a relative group law on $f_1$, that is, a group structure on the sets $\{\varphi : T \to A_1 \mid \varphi \circ f_1 = t\}$ of $T$-points over $\operatorname{Spec} B_1$, natural in $(T,t)$. Let $D_0$ and $D$ be bare deformations of $(f_1, L_1)$ over $B$: each consists of a scheme $A$ with a morphism $f : A \to \operatorname{Spec} B$ that is smooth and proper with connected fibres and admits a relative group law, a commutative relative group law $L$ on $f$, and a morphism $g : A_1 \to A$ exhibiting $f_1$ as the base change of $f$ along $\operatorname{Spec} B_1 \to \operatorname{Spec} B$ and compatible with the multiplications of $L_1$ and $L$. Let $\mathcal{U}$ be an ordered affine cover of $D_0.A$: a finite linearly ordered index set $\iota$, affine opens $U_i$ with $\bigsqcup_i U_i = \top$. The assertion is that there is a family $\tau$ assigning to each strictly monotone $s : \{0,1\} \to \iota$ (so each pair $s(0) < s(1)$) a self-isomorphism $\tau_s$ of the scheme $U_{s(0)} \cap U_{s(1)}$ such that `D₀.IsRegluingBy 𝒰 τ D` holds, namely: each $\tau_s$ is a morphism over $B$, in the sense that $\tau_s$ followed by the inclusion of the intersection and $D_0.f$ equals the inclusion followed by $D_0.f$; the restriction of $D_0.g$ over the intersection followed by $\tau_s$ equals that restriction; and there are morphisms $\iota_i : U_i \to D.A$ which are open immersions, satisfy $D.f \circ \iota_i = D_0.f$ on $U_i$, are jointly surjective on points of $D.A$, are compatible with $D_0.g$ and $D.g$ on the preimages of the $U_i$, and glue along $\tau$: on $U_{s(0)} \cap U_{s(1)}$ the map $\iota_{s(0)}$ equals $\tau_s$ followed by $\iota_{s(1)}$.
--
--   This is the local triviality of deformations of a smooth proper scheme across a nilpotent thickening, in the form needed here: any two bare deformations of the same pair $(f_1, L_1)$ differ only by re-gluing the charts of a fixed finite affine cover by automorphisms of the pairwise overlaps that are trivial modulo the thickening. It feeds the construction of tangent coordinates for pairs of bare deformations, and through that the comparison of deformations used in the good reduction analysis of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_isRegluingBy_of_bareDeformation_bare.lean

import Mathlib
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing

theorem GoodReductionJacobian.BareDeformation.exists_isRegluingBy_of_bareDeformation_bare
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)
    (D₀ : BareDeformation f₁ L₁ B) (𝒰 : D₀.A.OrderedAffineCover) (D : BareDeformation f₁ L₁ B) :
    ∃ τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)), D₀.IsRegluingBy 𝒰 τ D := by sorry
