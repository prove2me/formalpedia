-- Prove2me | Theorems.Thm_GlobalTheory_mul_comp_of_isGrpPullback
-- name    : GlobalTheory.mul_comp_of_isGrpPullback
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:12:36.029195+00:00
-- url     : https://prove2.me/theorems/da468315-f707-4dfe-a07f-ccf0638f148c
-- title:
--   Global Theory: mul comp of is Grp Pullback
-- statement:
--   The Global Theory construction uses the mul comp of is Grp Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GrpHomAlgebraisationOfReductions.lean#L26-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GrpHomAlgebraisationOfReductions.lean#L26-L40

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GrpHomAlgebraisationOfReductions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.mul_comp_of_isGrpPullback {S S' : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]
    {Y Z : Over S'} [GrpObj Y] [GrpObj Z] {t : S' ⟶ S} {a : Y.left ⟶ A.left} {b : Z.left ⟶ B.left}
    (ha : IsGrpPullback Y A t a) (hb : IsGrpPullback Z B t b) (f : Y ⟶ Z) [IsMonHom f] (g : A ⟶ B)
    (hg : a ≫ g.left = f.left ≫ b) (T : Over S') (x y : Over.mk (T.hom ≫ t) ⟶ A) :
    (x * y) ≫ g = (x ≫ g) * (y ≫ g) := by sorry
