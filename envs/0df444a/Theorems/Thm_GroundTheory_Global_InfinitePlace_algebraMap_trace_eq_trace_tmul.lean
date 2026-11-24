-- Prove2me | Theorems.Thm_GroundTheory_Global_InfinitePlace_algebraMap_trace_eq_trace_tmul
-- name    : GroundTheory.Global.InfinitePlace.algebraMap_trace_eq_trace_tmul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:39:31.621982+00:00
-- url     : https://prove2.me/theorems/d93ff9e0-9f0e-495d-9033-3705221b1ca3
-- title:
--   Infinite Place: algebra Map trace eq trace tmul
-- statement:
--   The Infinite Place construction uses the algebra Map trace eq trace tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Infinite.lean#L249-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Infinite.lean#L249-L253

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

theorem GroundTheory.Global.InfinitePlace.algebraMap_trace_eq_trace_tmul (l : L) :
    algebraMap K v.Completion (Algebra.trace K L l) =
      Algebra.trace v.Completion _ ((1 : v.Completion) ⊗ₜ[K] l) := by sorry
