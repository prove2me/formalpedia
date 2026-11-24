-- Prove2me | Theorems.Thm_GlobalTheory_ExtendRig_isRegularRing_of_isDiscreteValuationRing
-- name    : GlobalTheory.ExtendRig.isRegularRing_of_isDiscreteValuationRing
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:17:43.453797+00:00
-- url     : https://prove2.me/theorems/1bed9764-377d-477a-ae0b-ccbb0223a2b4
-- title:
--   Extend Rig: is Regular Ring of is Discrete Valuation Ring
-- statement:
--   The Extend Rig construction uses the is Regular Ring of is Discrete Valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsRegularRingOfIsDiscreteValuationRing.lean#L24-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsRegularRingOfIsDiscreteValuationRing.lean#L24-L27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfIsDiscreteValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ExtendRig

theorem GlobalTheory.ExtendRig.isRegularRing_of_isDiscreteValuationRing (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] : IsRegularRing V := by sorry
