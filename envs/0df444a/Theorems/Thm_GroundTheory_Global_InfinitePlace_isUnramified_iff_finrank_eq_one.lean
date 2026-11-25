-- Prove2me | Theorems.Thm_GroundTheory_Global_InfinitePlace_isUnramified_iff_finrank_eq_one
-- name    : GroundTheory.Global.InfinitePlace.isUnramified_iff_finrank_eq_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:14:51.384854+00:00
-- url     : https://prove2.me/theorems/74c82ace-d5c5-4610-8570-9bf371d12886
-- title:
--   Infinite Place: is Unramified iff finrank eq one
-- statement:
--   The Infinite Place construction uses the is Unramified iff finrank eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/SplittingInfinite.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/KummerTheory/SplittingInfinite.lean#L21-L26

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingInfinite
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

theorem GroundTheory.Global.InfinitePlace.isUnramified_iff_finrank_eq_one (w : NumberField.InfinitePlace L) [w.LiesOver v] :
    w.IsUnramified K ↔ finrank v.Completion w.Completion = 1 := by sorry
