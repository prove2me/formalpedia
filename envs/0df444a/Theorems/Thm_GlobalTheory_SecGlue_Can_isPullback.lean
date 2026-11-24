-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Can_isPullback
-- name    : GlobalTheory.SecGlue.Can.isPullback
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:48:47.799649+00:00
-- url     : https://prove2.me/theorems/6f074cf0-2470-418a-9a24-b1e2314a7b84
-- title:
--   Can: is Pullback
-- statement:
--   The Can construction uses the is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueGlueSectionsPrincipalCover.lean#L203-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsUniqueGlueSectionsPrincipalCover.lean#L203-L212

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUniqueGlueSectionsPrincipalCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
open TopologicalSpace
open GlobalTheory GlobalTheory.SecGlue
variable {B : Scheme.{0}} (G : Over B) {S T : Scheme.{0}}
variable {G}

theorem GlobalTheory.SecGlue.Can.isPullback {f : T ⟶ S} {x : S ⟶ B} {x' : T ⟶ B} (e : f ≫ x = x') {pm}
    (h : Can G f x x' pm) :
    IsPullback pm (fst (Over.mk x') G).left (fst (Over.mk x) G).left f := by sorry
