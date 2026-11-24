-- Prove2me | Theorems.Thm_GlobalTheory_FiniteEndFlat_apply_genericPoint
-- name    : GlobalTheory.FiniteEndFlat.apply_genericPoint
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:30:16.326065+00:00
-- url     : https://prove2.me/theorems/215768e8-42c9-4199-8ad0-c44e667b7277
-- title:
--   Finite End Flat: apply generic Point
-- statement:
--   The Finite End Flat construction uses the apply generic Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FlatAndSurjectiveOfIsFiniteAbelianEnd.lean#L26-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FlatAndSurjectiveOfIsFiniteAbelianEnd.lean#L26-L45

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

theorem GlobalTheory.FiniteEndFlat.apply_genericPoint {X : Scheme.{0}} [IrreducibleSpace X] [IsLocallyNoetherian X]
    (f : X ⟶ X) [LocallyQuasiFinite f] {o : X} (ho : f o = o) :
    f (genericPoint X) = genericPoint X := by sorry
