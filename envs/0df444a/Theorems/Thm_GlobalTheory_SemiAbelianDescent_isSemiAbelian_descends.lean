-- Prove2me | Theorems.Thm_GlobalTheory_SemiAbelianDescent_isSemiAbelian_descends
-- name    : GlobalTheory.SemiAbelianDescent.isSemiAbelian_descends
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:54:27.536208+00:00
-- url     : https://prove2.me/theorems/ff68716a-e882-49e3-a6ae-3def8a8633e1
-- title:
--   Semi Abelian Descent: is Semi Abelian descends
-- statement:
--   The Semi Abelian Descent construction uses the is Semi Abelian descends property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GeometricallyConnectedOfIsPullback.lean#L98-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GeometricallyConnectedOfIsPullback.lean#L98-L121

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_OneArc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GeometricallyConnectedOfIsPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.SemiAbelianDescent

theorem GlobalTheory.SemiAbelianDescent.isSemiAbelian_descends {X X' : Scheme.{0}} {π : X ⟶ X'} {G : Over X} [GrpObj G] {G' : Over X'}
    [GrpObj G'] [IsCommMonObj G'] {φ : G.left ⟶ G'.left} [IsIntegralHom π] [Surjective π]
    (h : IsGrpPullback G G' π φ) [Smooth G'.hom] (hG : IsSemiAbelian G) : IsSemiAbelian G' := by sorry
