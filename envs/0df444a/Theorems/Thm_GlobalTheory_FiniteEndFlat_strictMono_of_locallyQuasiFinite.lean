-- Prove2me | Theorems.Thm_GlobalTheory_FiniteEndFlat_strictMono_of_locallyQuasiFinite
-- name    : GlobalTheory.FiniteEndFlat.strictMono_of_locallyQuasiFinite
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:30:46.201155+00:00
-- url     : https://prove2.me/theorems/94af6a79-75a4-47eb-854c-a945382229d5
-- title:
--   Finite End Flat: strict Mono of locally Quasi Finite
-- statement:
--   The Finite End Flat construction uses the strict Mono of locally Quasi Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FlatAndSurjectiveOfIsFiniteAbelianEnd.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FlatAndSurjectiveOfIsFiniteAbelianEnd.lean#L15-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FlatOfFormallyUnramifiedGrpEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.FiniteEndFlat

theorem GlobalTheory.FiniteEndFlat.strictMono_of_locallyQuasiFinite {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyQuasiFinite f] :
    StrictMono (f : X → Y) := by sorry
