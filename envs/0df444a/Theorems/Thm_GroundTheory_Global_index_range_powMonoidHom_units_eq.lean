-- Prove2me | Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom_units_eq
-- name    : GroundTheory.Global.index_range_powMonoidHom_units_eq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:41:32.902137+00:00
-- url     : https://prove2.me/theorems/7fa19bd8-1191-43f6-b78d-ce186a9eab1f
-- title:
--   Global: index range pow Monoid Hom units eq
-- statement:
--   The Global construction uses the index range pow Monoid Hom units eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L298-L312
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L298-L312

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

theorem GroundTheory.Global.index_range_powMonoidHom_units_eq {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) (n : ℕ) :
    (powMonoidHom n : Kˣ →* Kˣ).range.index =
      n * (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range.index := by sorry
