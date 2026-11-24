-- Prove2me | Theorems.Thm_GroundTheory_Global_eq_one_of_sq_mem
-- name    : GroundTheory.Global.eq_one_of_sq_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:42.023669+00:00
-- url     : https://prove2.me/theorems/cfa7d3ed-f035-47b1-bf90-0fabdd7959fa
-- title:
--   Global: eq one of sq mem
-- statement:
--   The Global construction uses the eq one of sq mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L42-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L42-L49

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
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
open Topology Filter

theorem GroundTheory.Global.eq_one_of_sq_mem {s : Set ℂ} (hsq : ∀ z ∈ s, z ^ 2 ∈ s)
    (hs : ∀ z ∈ s, ‖z - 1‖ < 1 / 2) {z : ℂ} (hz : z ∈ s) : z = 1 := by sorry
