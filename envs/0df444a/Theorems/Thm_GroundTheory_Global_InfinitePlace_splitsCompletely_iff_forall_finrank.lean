-- Prove2me | Theorems.Thm_GroundTheory_Global_InfinitePlace_splitsCompletely_iff_forall_finrank
-- name    : GroundTheory.Global.InfinitePlace.splitsCompletely_iff_forall_finrank
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T02:04:20.626605+00:00
-- url     : https://prove2.me/theorems/58f1e5a3-2294-5f77-8865-a2cda128575e
-- title:
--   Infinite Place: splits Completely iff forall finrank
-- statement:
--   The Infinite Place construction uses the splits Completely iff forall finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/SplittingInfinite.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/SplittingInfinite.lean#L28-L32

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingInfinite
import Theorems.Thm_GroundTheory_Global_splitsCompletely_iff_forall_finrank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open NumberField Module
open scoped NumberField.LiesOver TensorProduct
open GroundTheory.Global.InfinitePlace
variable {K : Type*} [Field K] (L : Type*) [Field L] [Algebra K L]
variable {L} (v : NumberField.InfinitePlace K)

theorem GroundTheory.Global.InfinitePlace.splitsCompletely_iff_forall_finrank :
    SplitsCompletely L v ↔
      ∀ w : v.placesOver L, finrank v.Completion (w : NumberField.InfinitePlace L).Completion = 1 := by sorry
