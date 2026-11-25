-- Prove2me | Theorems.Thm_GroundTheory_Global_pow_mem_unitFiltration
-- name    : GroundTheory.Global.pow_mem_unitFiltration
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:42:03.011771+00:00
-- url     : https://prove2.me/theorems/e4faa991-f537-4fc1-aa51-f36fa2f05bb8
-- title:
--   Global: pow mem unit Filtration
-- statement:
--   The Global construction uses the pow mem unit Filtration property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L118-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L118-L123

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

theorem GroundTheory.Global.pow_mem_unitFiltration {j : ℕ} (hj : d + 1 ≤ j) {u : 𝒪[K]ˣ}
    (hu : u ∈ unitFiltration K j) : u ^ n ∈ unitFiltration K (j + d) := by sorry
