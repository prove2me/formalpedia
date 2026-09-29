-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_relativeGroupLaw_mul_eq_mul_genPt_of_one_eq
-- name    : ModularCurve.JHNeronObjectAtP.relativeGroupLaw_mul_eq_mul_genPt_of_one_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/a945b9e9-8a52-5c8e-b2ee-423c3b435f23
-- title:
--   Two relative group laws with equal unit agree at genPt
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a proof $hpM$ that $p \mid M$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $A.\mathrm{LiesOverPrime}\ p$, i.e. the image of $p$ lies in the nonunits of $A$, and assume the residue field of $A$ has characteristic $p$ and is algebraically closed. Let $\Lambda$ be level data of type `JHNeronObjectAtP.LevelData p M H hpM A` and let $O$ be a term of `JHNeronObjectAtP p M H hpM A hA Λ`; in particular $O$ provides a scheme $O.G$ with a morphism $O.g : O.G \to \mathrm{Spec}\,(\mathrm{baseRing}\ p)$ which is smooth, separated, locally of finite type, quasi-compact and surjective with preconnected fibres and proper generic fibre, together with a commutative relative group law $O.L$ on the functor of points of $O.g$. Let $L_2$ be any further relative group law on $O.g$ over $\mathrm{baseRing}\ p$, and assume that for every scheme $T$ and every morphism $s : T \to \mathrm{Spec}\,(\mathrm{baseRing}\ p)$ the unit section of $L_2$ at $s$ has the same underlying morphism $T \to O.G$ as that of $O.L$. Then for all sections $x, y$ of $O.g$ over the geometric generic point $\mathrm{genPt}\ p$ (morphisms $\mathrm{Spec}\,\overline{\mathbb{Q}} \to O.G$ composing with $O.g$ to the map induced by $\mathrm{baseRing}\ p \to \overline{\mathbb{Q}}$), the underlying morphisms of $L_2.\mathrm{mul}$ and of $O.L.\mathrm{mul}$ applied to $x$ and $y$ coincide.
--
--   This is the rigidity statement for abelian varieties in the form needed here: on the generic fibre, which is a smooth proper connected group scheme over $\mathbb{Q}$ with a rational point, a group law is determined by its unit section, so two relative group laws on the Néron object for $J_H(M)$ at $p \mid M$ sharing a unit agree on $\overline{\mathbb{Q}}$-points. No equality of the two laws over the whole base is asserted. It is used when comparing a group law transported from elsewhere with the law carried by the Néron object, in particular in the construction of the additive isomorphism matching toric and finite points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_relativeGroupLaw_mul_eq_mul_genPt_of_one_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.relativeGroupLaw_mul_eq_mul_genPt_of_one_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (L₂ : RelativeGroupLaw (baseRing p) O.g)
    (hone : ∀ {T : Scheme.{0}} (s : T ⟶ base p), (L₂.one s).1 = (O.L.one s).1) :
    ∀ x y : SchemeHomOver (genPt p) O.g, (L₂.mul _ x y).1 = (O.L.mul _ x y).1 := by sorry
