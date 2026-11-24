-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_one_add_uniformizer_pow_mul_pow_eq
-- name    : GroundTheory.Global.exists_one_add_uniformizer_pow_mul_pow_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:41:07.985808+00:00
-- url     : https://prove2.me/theorems/e7fd7cf7-c6bc-4d3f-a027-dbc6ce97e671
-- title:
--   Global: exists one add uniformizer pow mul pow eq
-- statement:
--   The Global construction uses the exists one add uniformizer pow mul pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L101-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L101-L107

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
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] hϖ

theorem GroundTheory.Global.exists_one_add_uniformizer_pow_mul_pow_eq {j : ℕ} (hj : d + 1 ≤ j) (a : 𝒪[K]) :
    ∃ c : 𝒪[K], (1 + ϖ ^ j * a) ^ n = 1 + ϖ ^ (j + d) * (ε * a + ϖ * c) := by sorry
