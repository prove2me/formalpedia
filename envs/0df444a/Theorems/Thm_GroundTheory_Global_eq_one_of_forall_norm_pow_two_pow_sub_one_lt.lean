-- Prove2me | Theorems.Thm_GroundTheory_Global_eq_one_of_forall_norm_pow_two_pow_sub_one_lt
-- name    : GroundTheory.Global.eq_one_of_forall_norm_pow_two_pow_sub_one_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:22.28403+00:00
-- url     : https://prove2.me/theorems/23807887-4c3e-41bb-97b2-1803bdea17d8
-- title:
--   Global: eq one of forall norm pow two pow sub one lt
-- statement:
--   The Global construction uses the eq one of forall norm pow two pow sub one lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L23-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L23-L40

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

theorem GroundTheory.Global.eq_one_of_forall_norm_pow_two_pow_sub_one_lt {z : ℂ}
    (hz : ∀ k : ℕ, ‖z ^ (2 ^ k) - 1‖ < 1 / 2) : z = 1 := by sorry
