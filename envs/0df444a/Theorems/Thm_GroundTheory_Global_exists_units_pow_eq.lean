-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_units_pow_eq
-- name    : GroundTheory.Global.exists_units_pow_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:08.961524+00:00
-- url     : https://prove2.me/theorems/c3e9e0bd-b7cf-499a-abb6-77dbf4a3f365
-- title:
--   Global: exists units pow eq
-- statement:
--   The Global construction uses the exists units pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L111-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L111-L116

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

theorem GroundTheory.Global.exists_units_pow_eq {j : ℕ} (hj : d + 1 ≤ j) {u : 𝒪[K]ˣ} {a : 𝒪[K]}
    (hu : (u : 𝒪[K]) - 1 = ϖ ^ j * a) :
    ∃ c : 𝒪[K], ((u ^ n : 𝒪[K]ˣ) : 𝒪[K]) = 1 + ϖ ^ (j + d) * (ε * a + ϖ * c) := by sorry
