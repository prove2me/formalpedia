-- Prove2me | Theorems.Thm_GroundTheory_Global_InfinitePlace_trace_tensor_eq_sum
-- name    : GroundTheory.Global.InfinitePlace.trace_tensor_eq_sum
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:39:22.287388+00:00
-- url     : https://prove2.me/theorems/b0af9bd1-436c-4e4c-b20b-f0435e2c0924
-- title:
--   Infinite Place: trace tensor eq sum
-- statement:
--   The Infinite Place construction uses the trace tensor eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Infinite.lean#L265-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Infinite.lean#L265-L269

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SemilocalAlgebras_Infinite
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
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open scoped NumberField.LiesOver TensorProduct
open GroundTheory.Global.InfinitePlace
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K)
variable [NumberField K] [NumberField L]
open scoped Classical

theorem GroundTheory.Global.InfinitePlace.trace_tensor_eq_sum (x : v.Completion ⊗[K] L) :
    Algebra.trace v.Completion _ x =
      ∑ w : v.placesOver L, Algebra.trace v.Completion _ (tensorPiHom v x w) := by sorry
