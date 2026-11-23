-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_mk_mem_kummerGroup
-- name    : GroundTheory.ProfCoh.mk_mem_kummerGroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:23.274259+00:00
-- url     : https://prove2.me/theorems/bb2acf04-3fe3-47e9-b52d-97c4be12fa18
-- title:
--   Prof Coh: mk mem kummer Group
-- statement:
--   The Prof Coh construction uses the mk mem kummer Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerBasic.lean#L56-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerBasic.lean#L56-L66

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open Polynomial
variable (K : Type*) [Field K] (n : ℕ)
variable (L : Type*) [Field L] [Algebra K L]
variable {K n L}

theorem GroundTheory.ProfCoh.mk_mem_kummerGroup {a : Kˣ} :
    (a : UnitsModPow K n) ∈ kummerGroup K n L ↔ ∃ α : L, α ^ n = algebraMap K L a := by sorry
