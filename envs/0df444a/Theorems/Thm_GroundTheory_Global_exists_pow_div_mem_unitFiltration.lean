-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_pow_div_mem_unitFiltration
-- name    : GroundTheory.Global.exists_pow_div_mem_unitFiltration
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:41:43.767439+00:00
-- url     : https://prove2.me/theorems/c134ad6f-e5e5-41c6-ae7c-74d8b1968e7c
-- title:
--   Global: exists pow div mem unit Filtration
-- statement:
--   The Global construction uses the exists pow div mem unit Filtration property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L125-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L125-L137

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

theorem GroundTheory.Global.exists_pow_div_mem_unitFiltration {j : ℕ} (hj : d + 1 ≤ j) {h : 𝒪[K]ˣ}
    (hh : h ∈ unitFiltration K (j + d)) :
    ∃ g ∈ unitFiltration K j, h / g ^ n ∈ unitFiltration K (j + 1 + d) := by sorry
