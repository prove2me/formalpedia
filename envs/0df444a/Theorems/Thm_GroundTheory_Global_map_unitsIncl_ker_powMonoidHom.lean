-- Prove2me | Theorems.Thm_GroundTheory_Global_map_unitsIncl_ker_powMonoidHom
-- name    : GroundTheory.Global.map_unitsIncl_ker_powMonoidHom
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:42:34.171768+00:00
-- url     : https://prove2.me/theorems/a8917642-52b2-4d5a-b372-1f234ee05aef
-- title:
--   Global: map units Incl ker pow Monoid Hom
-- statement:
--   The Global construction uses the map units Incl ker pow Monoid Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L236-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L236-L258

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
variable {n : ℕ}

theorem GroundTheory.Global.map_unitsIncl_ker_powMonoidHom (hn : n ≠ 0) :
    (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).ker.map (unitsIncl K) = rootsOfUnity n K := by sorry
