-- Prove2me | Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom_multiplicativeInt
-- name    : GroundTheory.Global.index_range_powMonoidHom_multiplicativeInt
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:41:18.364519+00:00
-- url     : https://prove2.me/theorems/4c8d6899-65fc-4906-ad84-396a98567a2b
-- title:
--   Global: index range pow Monoid Hom multiplicative Int
-- statement:
--   The Global construction uses the index range pow Monoid Hom multiplicative Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L266-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L266-L280

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
omit [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.Global.index_range_powMonoidHom_multiplicativeInt (n : ℕ) :
    (powMonoidHom n : Multiplicative ℤ →* Multiplicative ℤ).range.index = n := by sorry
