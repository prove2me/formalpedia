-- Prove2me | Theorems.Thm_GroundTheory_Global_infiniteDecompositionMulEquiv_apply
-- name    : GroundTheory.Global.infiniteDecompositionMulEquiv_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:08:29.861952+00:00
-- url     : https://prove2.me/theorems/7bb5e114-e302-4826-9f27-c596cb3a465e
-- title:
--   Global: infinite Decomposition Mul Equiv apply
-- statement:
--   The Global construction uses the infinite Decomposition Mul Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrandInfinite.lean#L198-L200
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrandInfinite.lean#L198-L200

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrand
import Definitions.Def_GroundTheory_GlobalFields_InfiniteNormIndex_LocalSymbol
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrandInfinite
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
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion GroundTheory.GroupCoh
open scoped NumberField.LiesOver
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K)
  (w : InfinitePlace L) [w.LiesOver v]
variable [IsGalois K L]

theorem GroundTheory.Global.infiniteDecompositionMulEquiv_apply (σ : MulAction.stabilizer Gal(L/K) w)
    (x : w.Completion) : infiniteDecompositionMulEquiv v w σ x = σ • x := by sorry

attribute [defeq] GroundTheory.Global.infiniteDecompositionMulEquiv_apply
