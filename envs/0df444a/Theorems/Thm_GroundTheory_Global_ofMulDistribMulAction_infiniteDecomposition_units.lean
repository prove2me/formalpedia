-- Prove2me | Theorems.Thm_GroundTheory_Global_ofMulDistribMulAction_infiniteDecomposition_units
-- name    : GroundTheory.Global.ofMulDistribMulAction_infiniteDecomposition_units
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:54:08.961715+00:00
-- url     : https://prove2.me/theorems/111bbb65-5356-4d1c-b087-d4b8854043ba
-- title:
--   Global: of Mul Distrib Mul Action infinite Decomposition units
-- statement:
--   The Global construction uses the of Mul Distrib Mul Action infinite Decomposition units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrandInfinite.lean#L240-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrandInfinite.lean#L240-L247

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

theorem GroundTheory.Global.ofMulDistribMulAction_infiniteDecomposition_units
    (σ : MulAction.stabilizer Gal(L/K) w) (x : Additive w.Completionˣ) :
    Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w) w.Completionˣ σ x =
      Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion) w.Completionˣ
        (infiniteDecompositionMulEquiv v w σ) x := by sorry
