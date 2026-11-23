-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_unitsPow_le_unitsPowIn
-- name    : GroundTheory.ProfCoh.unitsPow_le_unitsPowIn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:01:04.375817+00:00
-- url     : https://prove2.me/theorems/f3983bf5-e5e0-4027-ac01-43e1fabaca71
-- title:
--   Prof Coh: units Pow le units Pow In
-- statement:
--   The Prof Coh construction uses the units Pow le units Pow In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerBasic.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/KummerBasic.lean#L47-L50

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

theorem GroundTheory.ProfCoh.unitsPow_le_unitsPowIn : unitsPow K n ≤ unitsPowIn K n L := by sorry
