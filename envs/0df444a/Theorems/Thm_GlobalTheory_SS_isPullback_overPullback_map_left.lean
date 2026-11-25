-- Prove2me | Theorems.Thm_GlobalTheory_SS_isPullback_overPullback_map_left
-- name    : GlobalTheory.SS.isPullback_overPullback_map_left
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:09:43.473207+00:00
-- url     : https://prove2.me/theorems/50183086-9893-4622-8236-866134b60f6d
-- title:
--   SS: is Pullback over Pullback map left
-- statement:
--   The SS construction uses the is Pullback over Pullback map left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber.lean#L18-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber.lean#L18-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsAbelianSchemeAndExtendOfGenericHoms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
open GlobalTheory GlobalTheory.SS

theorem GlobalTheory.SS.isPullback_overPullback_map_left {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (q : X ⟶ Y) :
    IsPullback (pullback.fst X.hom f) ((Over.pullback f).map q).left q.left (pullback.fst Y.hom f) := by sorry
