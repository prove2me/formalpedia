-- Prove2me | Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_relativeGroupLaw_of_isPullback_of_smooth
-- name    : GoodReductionJacobian.BareDeformation.exists_relativeGroupLaw_of_isPullback_of_smooth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:52.294557+00:00
-- url     : https://prove2.me/theorems/c704fb87-2843-547b-a3fa-31ba76d01874
-- title:
--   Commutative group law on a smooth cartesian lift over B
-- statement:
--   Let $B$ be an Artinian local ring whose residue field is algebraically closed, and let $B_1$ be a $B$-algebra such that the structure map $B \to B_1$ is surjective, has nilpotent kernel $J$, and satisfies $J \cdot \mathfrak{m}_B = 0$. Let $f_1 \colon A_1 \to \operatorname{Spec} B_1$ be a morphism of schemes equipped with a relative group law $L_1$ over $B_1$, that is, a group structure on the set of sections $\{\varphi : T \to A_1 \mid \varphi \text{ followed by } f_1 = t\}$ for each $t \colon T \to \operatorname{Spec} B_1$, compatible with base change along $T' \to T$; assume $L_1$ is commutative and that $f_1$ satisfies the bundle of properties: smooth, proper, with connected fibres over every point of $\operatorname{Spec} B_1$, and admitting some relative group law. Let $f_X \colon X \to \operatorname{Spec} B$ be smooth and let $g_X \colon A_1 \to X$ make the square with $f_1$, $f_X$ and $\operatorname{Spec}(B \to B_1)$ cartesian. Then there exist a relative group law $L$ on $f_X$ over $B$, a proof that $L$ is commutative, and a proof that $f_X$ is smooth, proper, with connected fibres and carrying a group law, such that for every scheme $S$, every $t \colon S \to \operatorname{Spec} B_1$ and all sections $P, Q$ of $f_1$ over $t$, the product $L_1.\mathrm{mul}\,t\,P\,Q$ followed by $g_X$ coincides with the $L$-product, over $t$ followed by $\operatorname{Spec}(B \to B_1)$, of $P$ followed by $g_X$ and $Q$ followed by $g_X$.
--
--   This is the step asserting that a smooth cartesian lift of an abelian scheme across a small surjection $B \twoheadrightarrow B_1$ is again an abelian scheme, with a commutative group law whose restriction along $g_X$ is the given one; the conclusion is exactly in the shape of the fields of the `BareDeformation` structure. It is used in the construction of regluings and shifts of bare deformations at a tangent-coordinate pair.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_BareDeformation_exists_relativeGroupLaw_of_isPullback_of_smooth.lean

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

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover
open AlgebraicGeometry

open scoped Quaternion TensorProduct NumberField

theorem GoodReductionJacobian.BareDeformation.exists_relativeGroupLaw_of_isPullback_of_smooth
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [IsAlgClosed (ResidueField B)]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥)
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁) (hc₁ : L₁.IsCommutative)
    (h₁ : AbelianSchemePropertyBundle B₁ f₁)
    {X : Scheme.{0}} (fX : X ⟶ Spec (CommRingCat.of B)) (hsX : Smooth fX)
    (gX : A₁ ⟶ X) (hgX : IsPullback gX f₁ fX (Spec.map (CommRingCat.ofHom (algebraMap B B₁)))) :
    ∃ (L : RelativeGroupLaw B fX) (_ : L.IsCommutative) (_ : AbelianSchemePropertyBundle B fX),
      ∀ {S : Scheme.{0}} (t : S ⟶ Spec (CommRingCat.of B₁)) (P Q : SchemeHomOver t f₁),
        (L₁.mul t P Q).1 ≫ gX =
          (L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁)))
            ⟨P.1 ≫ gX, by rw [Category.assoc, hgX.w, ← Category.assoc, P.2]⟩
            ⟨Q.1 ≫ gX, by rw [Category.assoc, hgX.w, ← Category.assoc, Q.2]⟩).1 := by sorry
