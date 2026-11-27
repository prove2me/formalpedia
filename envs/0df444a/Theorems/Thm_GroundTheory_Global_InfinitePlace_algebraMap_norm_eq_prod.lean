-- Prove2me | Theorems.Thm_GroundTheory_Global_InfinitePlace_algebraMap_norm_eq_prod
-- name    : GroundTheory.Global.InfinitePlace.algebraMap_norm_eq_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:54:44.339926+00:00
-- url     : https://prove2.me/theorems/ee6185de-4bf6-5185-9bc4-ac51f44b5379
-- title:
--   Infinite Place: algebra Map norm eq prod
-- statement:
--   The Infinite Place construction uses the algebra Map norm eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Infinite.lean#L273-L277
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SemilocalAlgebras/Infinite.lean#L273-L277

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

theorem GroundTheory.Global.InfinitePlace.algebraMap_norm_eq_prod (l : L) :
    algebraMap K v.Completion (Algebra.norm K l) =
      ∏ w : v.placesOver L, Algebra.norm v.Completion (l : (w : InfinitePlace L).Completion) := by sorry
