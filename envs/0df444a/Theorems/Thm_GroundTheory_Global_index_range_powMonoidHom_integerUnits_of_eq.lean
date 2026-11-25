-- Prove2me | Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom_integerUnits_of_eq
-- name    : GroundTheory.Global.index_range_powMonoidHom_integerUnits_of_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:41:13.94684+00:00
-- url     : https://prove2.me/theorems/1d9c4b86-6d45-449a-b08c-cb24fc48ef12
-- title:
--   Global: index range pow Monoid Hom integer Units of eq
-- statement:
--   The Global construction uses the index range pow Monoid Hom integer Units of eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L178-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L178-L205

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
variable {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {n d : ℕ} {ε : 𝒪[K]ˣ}
  (hnd : (n : 𝒪[K]) = ε * ϖ ^ d)
include hϖ hnd

theorem GroundTheory.Global.index_range_powMonoidHom_integerUnits_of_eq :
    (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).range.index =
      Nat.card (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).ker * Nat.card 𝓀[K] ^ d := by sorry
