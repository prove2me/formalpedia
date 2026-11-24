-- Prove2me | Theorems.Thm_GroundTheory_Global_natCard_rootsOfUnity_eq
-- name    : GroundTheory.Global.natCard_rootsOfUnity_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:42:09.153047+00:00
-- url     : https://prove2.me/theorems/07cb6612-5769-4e56-95a8-cde0e8910ead
-- title:
--   Global: nat Card roots Of Unity eq
-- statement:
--   The Global construction uses the nat Card roots Of Unity eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L260-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L260-L262

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

theorem GroundTheory.Global.natCard_rootsOfUnity_eq (hn : n ≠ 0) :
    Nat.card (rootsOfUnity n K) = Nat.card (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).ker := by sorry
