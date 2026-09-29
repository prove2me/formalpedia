-- Prove2me | Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isAffineHom_flat_surjective_schemeNsmul_two_of_isFinite_flat_schemeKerStr
-- name    : GoodReductionJacobian.RelativeGroupLaw.isAffineHom_flat_surjective_schemeNsmul_two_of_isFinite_flat_schemeKerStr
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:53.637625+00:00
-- url     : https://prove2.me/theorems/6deedf8d-80dc-5431-840a-d8f86ce70516
-- title:
--   Multiplication by 2 on an abelian scheme is affine, flat, surjective
-- statement:
--   Let $S$ be a commutative ring, $A$ a scheme and $f : A \to \operatorname{Spec} S$ a morphism, and let $L$ be a `RelativeGroupLaw` for $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $A$-valued points over each $t : T \to \operatorname{Spec} S$, with multiplication, unit and inverse natural in $T$. Assume $L$ is commutative, that is, the multiplication on every such set of points is commutative, and assume the bundle `AbelianSchemePropertyBundle S f`: $f$ is smooth, $f$ is proper, each set-theoretic fibre $f^{-1}(s) \subseteq A$ over a point $s$ of $\operatorname{Spec} S$ is connected, and $f$ admits a relative group law. Assume further that the structure morphism $L.\mathrm{schemeKerStr}\,2 : A[2] \to \operatorname{Spec} S$ of the fibre product of $L.\mathrm{schemeNsmul}\,2$ with the unit section is finite, flat and locally of finite presentation. Then the morphism $L.\mathrm{schemeNsmul}\,2 : A \to A$, the underlying morphism of the double of the identity point of $A$ over $f$, is an affine morphism, flat and surjective.
--
--   This is the statement that multiplication by $2$ on an abelian scheme over an arbitrary affine base is affine, flat and surjective. It feeds the treatment of polarisations, being used in the construction of a $2$-torsion character with a bijectivity property on symmetric rigidified line bundles and in the comparison of the negation morphism with the self-tensor square.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_RelativeGroupLaw_isAffineHom_flat_surjective_schemeNsmul_two_of_isFinite_flat_schemeKerStr.lean

import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_TorsionCharacter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicGeometry.Polarisation AlgebraicGeometry.RelPicard

theorem GoodReductionJacobian.RelativeGroupLaw.isAffineHom_flat_surjective_schemeNsmul_two_of_isFinite_flat_schemeKerStr
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (hker : IsFinite (L.schemeKerStr 2) ∧ Flat (L.schemeKerStr 2) ∧ LocallyOfFinitePresentation (L.schemeKerStr 2)) :
    IsAffineHom (L.schemeNsmul 2) ∧ Flat (L.schemeNsmul 2) ∧ Surjective (L.schemeNsmul 2) := by sorry
