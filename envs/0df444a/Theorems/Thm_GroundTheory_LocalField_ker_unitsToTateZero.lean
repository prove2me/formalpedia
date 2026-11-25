-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ker_unitsToTateZero
-- name    : GroundTheory.LocalField.ker_unitsToTateZero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:15:38.859185+00:00
-- url     : https://prove2.me/theorems/17dacd69-c5b3-4106-8da2-1be90690e470
-- title:
--   Local Field: ker units To Tate Zero
-- statement:
--   The Local Field construction uses the ker units To Tate Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandLocalBase.lean#L42-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandLocalBase.lean#L42-L54

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

theorem GroundTheory.LocalField.ker_unitsToTateZero : (unitsToTateZero (K := K) (L := L)).ker = (normUnits K L).range := by sorry
