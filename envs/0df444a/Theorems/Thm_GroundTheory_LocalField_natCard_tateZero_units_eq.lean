-- Prove2me | Theorems.Thm_GroundTheory_LocalField_natCard_tateZero_units_eq
-- name    : GroundTheory.LocalField.natCard_tateZero_units_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:16:15.825834+00:00
-- url     : https://prove2.me/theorems/af4b7220-be24-433f-a1cc-9ce8dc6bfaac
-- title:
--   Local Field: nat Card tate Zero units eq
-- statement:
--   The Local Field construction uses the nat Card tate Zero units eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandLocalBase.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandLocalBase.lean#L56-L59

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

theorem GroundTheory.LocalField.natCard_tateZero_units_eq :
    Nat.card (TateZero (L ≃ₐ[K] L) Lˣ) = Nat.card (Kˣ ⧸ (normUnits K L).range) := by sorry
