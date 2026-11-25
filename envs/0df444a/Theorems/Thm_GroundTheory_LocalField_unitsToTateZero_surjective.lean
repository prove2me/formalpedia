-- Prove2me | Theorems.Thm_GroundTheory_LocalField_unitsToTateZero_surjective
-- name    : GroundTheory.LocalField.unitsToTateZero_surjective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:16:40.777413+00:00
-- url     : https://prove2.me/theorems/907a5c16-ac4b-4250-9b2a-d90b1e3a181c
-- title:
--   Local Field: units To Tate Zero surjective
-- statement:
--   The Local Field construction uses the units To Tate Zero surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandLocalBase.lean#L30-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandLocalBase.lean#L30-L40

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
import Definitions.Def_GroundTheory_LocalFields_UnitsGalois
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeAndRangePowLe
import Definitions.Def_GroundTheory_LocalFields_ExistsUnitFiltrationUnitsLeRangeNormUnits
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocalBase
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
open ValuativeRel GroundTheory.GroupCoh GroundTheory.Global
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem GroundTheory.LocalField.unitsToTateZero_surjective : Function.Surjective (unitsToTateZero (K := K) (L := L)) := by sorry
