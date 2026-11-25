-- Prove2me | Theorems.Thm_GroundTheory_Global_uniformizer_pow_succ_dvd_of_valuation_lt
-- name    : GroundTheory.Global.uniformizer_pow_succ_dvd_of_valuation_lt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:43:04.910041+00:00
-- url     : https://prove2.me/theorems/476255ec-eecd-4216-a34b-01ab2bd55b4f
-- title:
--   Global: uniformizer pow succ dvd of valuation lt
-- statement:
--   The Global construction uses the uniformizer pow succ dvd of valuation lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L336-L352
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L336-L352

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

theorem GroundTheory.Global.uniformizer_pow_succ_dvd_of_valuation_lt {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) {k : ℕ}
    {z : 𝒪[K]} (h : valuation K (z : K) < valuation K ((ϖ : K) ^ k)) : ϖ ^ (k + 1) ∣ z := by sorry
