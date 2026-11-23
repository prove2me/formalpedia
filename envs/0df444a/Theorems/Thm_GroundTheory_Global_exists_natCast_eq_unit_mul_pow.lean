-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_natCast_eq_unit_mul_pow
-- name    : GroundTheory.Global.exists_natCast_eq_unit_mul_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:55.293801+00:00
-- url     : https://prove2.me/theorems/fbb7ae26-c704-4eda-97c5-e6a34517a40f
-- title:
--   Global: exists nat Cast eq unit mul pow
-- statement:
--   The Global construction uses the exists nat Cast eq unit mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L222-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/LocalIndex.lean#L222-L234

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

theorem GroundTheory.Global.exists_natCast_eq_unit_mul_pow (hn : (n : K) ≠ 0) {ϖ : 𝒪[K]} (hϖ : Irreducible ϖ) :
    ∃ (d : ℕ) (ε : 𝒪[K]ˣ), (n : 𝒪[K]) = ε * ϖ ^ d ∧ ord (n : K) = d := by sorry
