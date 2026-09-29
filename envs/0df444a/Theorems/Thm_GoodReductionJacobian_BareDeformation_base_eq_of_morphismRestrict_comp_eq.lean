-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_base_eq_of_morphismRestrict_comp_eq
-- name    : GoodReductionJacobian.BareDeformation.base_eq_of_morphismRestrict_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/39c05402-b72d-5e55-bb62-64e2327e1d95
-- title:
--   Endomorphism of an open fixing a nilpotent thickening's reduction is pointwise trivial
-- statement:
--   Let $B$ and $B_1$ be commutative rings with $B_1$ a $B$-algebra such that the structure map $B \to B_1$ is surjective and its kernel is a nilpotent ideal. Let $A_1$ be a scheme, $f_1 \colon A_1 \to \operatorname{Spec} B_1$ a morphism and $L_1$ a relative group law on $f_1$ over $B_1$, that is, functorially compatible multiplication, unit and inverse operations on the sets of $T$-points of $f_1$ over each $T \to \operatorname{Spec} B_1$, satisfying the group axioms and natural in $T$. Let $D_0$ be a bare deformation of $(f_1, L_1)$ over $B$: a scheme $D_0.A$ with a morphism $D_0.f \colon D_0.A \to \operatorname{Spec} B$ carrying a commutative relative group law, with $D_0.f$ smooth and proper with connected fibres and admitting a relative group law, together with a morphism $g \colon A_1 \to D_0.A$ making the square formed by $g$, $f_1$, $D_0.f$ and $\operatorname{Spec}(B \to B_1)$ cartesian and compatible with the two group laws. Let $W$ be an open subscheme of $D_0.A$ and $\alpha \colon W \to W$ a morphism such that the restriction $g \mid_W$ followed by $\alpha$ equals $g \mid_W$. Then $\alpha$ acts as the identity on the underlying topological space of $W$: $\alpha(x) = x$ for every point $x$ of $W$.
--
--   This is the pointwise rigidity step used when gluing: a self-map of an open subscheme of a nilpotent thickening that is compatible with the closed-fibre comparison map is the identity on points. It is used in the construction of a glued scheme from isomorphisms over overlaps, [`GoodReductionJacobian.BareDeformation.exists_glued_scheme_of_overlap_isos`](thm.html#GoodReductionJacobian.BareDeformation.exists_glued_scheme_of_overlap_isos).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_base_eq_of_morphismRestrict_comp_eq.lean

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

theorem GoodReductionJacobian.BareDeformation.base_eq_of_morphismRestrict_comp_eq
    (B B₁ : Type) [CommRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁)
    (D₀ : BareDeformation f₁ L₁ B) (W : D₀.A.Opens)
    (α : (↑W : Scheme.{0}) ⟶ ↑W) (hα : (D₀.g ∣_ W) ≫ α = D₀.g ∣_ W) :
    ∀ x : ↑W, α.base x = x := by sorry
