-- Prove2me | Theorems.Thm_GroundTheory_Global_eq_one_of_pow_eq_one
-- name    : GroundTheory.Global.eq_one_of_pow_eq_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:40:16.917486+00:00
-- url     : https://prove2.me/theorems/b907a1f0-555d-483d-afe5-16e4451fe8a8
-- title:
--   Global: eq one of pow eq one
-- statement:
--   The Global construction uses the eq one of pow eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L139-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L139-L168

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

theorem GroundTheory.Global.eq_one_of_pow_eq_one {u : 𝒪[K]ˣ} (hu : u ∈ unitFiltration K (d + 1)) (hun : u ^ n = 1) :
    u = 1 := by sorry
