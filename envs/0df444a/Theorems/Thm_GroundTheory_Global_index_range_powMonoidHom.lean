-- Prove2me | Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom
-- name    : GroundTheory.Global.index_range_powMonoidHom
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:41:40.980367+00:00
-- url     : https://prove2.me/theorems/3a0bcaf7-8116-4f14-b2e5-13afc759546c
-- title:
--   Global: index range pow Monoid Hom
-- statement:
--   The Global construction uses the index range pow Monoid Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L324-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L324-L330

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

theorem GroundTheory.Global.index_range_powMonoidHom (hn : (n : K) ≠ 0) :
    ((powMonoidHom n : Kˣ →* Kˣ).range.index : ℝ) =
      n * Nat.card (rootsOfUnity n K) * (Nat.card 𝓀[K] : ℝ) ^ ord (n : K) := by sorry
