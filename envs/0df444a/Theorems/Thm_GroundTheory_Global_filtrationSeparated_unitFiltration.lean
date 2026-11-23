-- Prove2me | Theorems.Thm_GroundTheory_Global_filtrationSeparated_unitFiltration
-- name    : GroundTheory.Global.filtrationSeparated_unitFiltration
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:14.756105+00:00
-- url     : https://prove2.me/theorems/3758842b-a988-4e2a-abb0-e8cb54cc45bf
-- title:
--   Global: filtration Separated unit Filtration
-- statement:
--   The Global construction uses the filtration Separated unit Filtration property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L46-L50

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_LocalIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open ValuativeRel IsLocalRing GroundTheory.LocalField
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.Global.filtrationSeparated_unitFiltration : FiltrationSeparated (unitFiltration K) := by sorry
