-- Prove2me | Theorems.Thm_GroundTheory_Global_index_range_powMonoidHom_eq_mul
-- name    : GroundTheory.Global.index_range_powMonoidHom_eq_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:41:18.652792+00:00
-- url     : https://prove2.me/theorems/ed6814dd-e0bf-4655-a537-f05838669ab4
-- title:
--   Global: index range pow Monoid Hom eq mul
-- statement:
--   The Global construction uses the index range pow Monoid Hom eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L314-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L314-L322

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

theorem GroundTheory.Global.index_range_powMonoidHom_eq_mul (hn : (n : K) ≠ 0) :
    ∃ d : ℕ, ord (n : K) = d ∧ (powMonoidHom n : Kˣ →* Kˣ).range.index =
      n * Nat.card (rootsOfUnity n K) * Nat.card 𝓀[K] ^ d := by sorry
