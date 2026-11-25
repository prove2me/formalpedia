-- Prove2me | Theorems.Thm_GroundTheory_Global_InfinitePlace_splitsCompletely_iff_isFiniteSplit
-- name    : GroundTheory.Global.InfinitePlace.splitsCompletely_iff_isFiniteSplit
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:55:07.666271+00:00
-- url     : https://prove2.me/theorems/ab310109-0bbd-52ee-94fa-14c982d586f8
-- title:
--   Infinite Place: splits Completely iff is Finite Split
-- statement:
--   The Infinite Place construction uses the splits Completely iff is Finite Split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/SplittingInfinite.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/SplittingInfinite.lean#L36-L40

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingInfinite
import Theorems.Thm_GroundTheory_Global_splitsCompletely_iff_isFiniteSplit

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
variable [NumberField K] [NumberField L]

theorem GroundTheory.Global.InfinitePlace.splitsCompletely_iff_isFiniteSplit :
    SplitsCompletely L v ↔ Algebra.IsFiniteSplit v.Completion (v.Completion ⊗[K] L) := by sorry
