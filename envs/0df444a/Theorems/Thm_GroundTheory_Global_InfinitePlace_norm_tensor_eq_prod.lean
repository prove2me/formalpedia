-- Prove2me | Theorems.Thm_GroundTheory_Global_InfinitePlace_norm_tensor_eq_prod
-- name    : GroundTheory.Global.InfinitePlace.norm_tensor_eq_prod
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:39:43.073831+00:00
-- url     : https://prove2.me/theorems/dcffe798-fc94-4d1b-ae61-2cf6a844a941
-- title:
--   Infinite Place: norm tensor eq prod
-- statement:
--   The Infinite Place construction uses the norm tensor eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Infinite.lean#L257-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Infinite.lean#L257-L261

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

theorem GroundTheory.Global.InfinitePlace.norm_tensor_eq_prod (x : v.Completion ⊗[K] L) :
    Algebra.norm v.Completion x =
      ∏ w : v.placesOver L, Algebra.norm v.Completion (tensorPiHom v x w) := by sorry
