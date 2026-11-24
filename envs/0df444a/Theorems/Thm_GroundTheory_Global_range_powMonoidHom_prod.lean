-- Prove2me | Theorems.Thm_GroundTheory_Global_range_powMonoidHom_prod
-- name    : GroundTheory.Global.range_powMonoidHom_prod
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:42:16.633557+00:00
-- url     : https://prove2.me/theorems/db429af4-d933-48df-a48c-c9a6120df415
-- title:
--   Global: range pow Monoid Hom prod
-- statement:
--   The Global construction uses the range pow Monoid Hom prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L284-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L284-L296

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

theorem GroundTheory.Global.range_powMonoidHom_prod {G H : Type*} [CommGroup G] [CommGroup H] (n : ℕ) :
    (powMonoidHom n : G × H →* G × H).range =
      (powMonoidHom n : G →* G).range.prod (powMonoidHom n : H →* H).range := by sorry
