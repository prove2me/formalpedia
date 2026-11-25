-- Prove2me | Theorems.Thm_GroundTheory_LocalField_setOf_ord_eq
-- name    : GroundTheory.LocalField.setOf_ord_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:45:20.932183+00:00
-- url     : https://prove2.me/theorems/0ec149ab-fc89-4af4-9631-6fc53f05935a
-- title:
--   Local Field: set Of ord eq
-- statement:
--   The Local Field construction uses the set Of ord eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeRangeNormUnits.lean#L66-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/ExistsUnitFiltrationUnitsLeRangeNormUnits.lean#L66-L74

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing Topology Filter Polynomial
open scoped WithZero nonZeroDivisors
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.setOf_ord_eq {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (m : ℤ) :
    {y : Kˣ | ord (y : K) = m} =
      (Homeomorph.mulLeft (uniformizerUnit hϖ ^ (-m))) ⁻¹' (unitFiltrationUnits K 0 : Set Kˣ) := by sorry
