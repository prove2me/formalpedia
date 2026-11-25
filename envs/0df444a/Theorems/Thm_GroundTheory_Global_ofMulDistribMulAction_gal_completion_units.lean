-- Prove2me | Theorems.Thm_GroundTheory_Global_ofMulDistribMulAction_gal_completion_units
-- name    : GroundTheory.Global.ofMulDistribMulAction_gal_completion_units
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:58:07.707262+00:00
-- url     : https://prove2.me/theorems/e4ee81ca-8468-41b5-bc81-8569bbcee931
-- title:
--   Global: of Mul Distrib Mul Action gal completion units
-- statement:
--   The Global construction uses the of Mul Distrib Mul Action gal completion units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrandInfinite.lean#L209-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrandInfinite.lean#L209-L215

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

theorem GroundTheory.Global.ofMulDistribMulAction_gal_completion_units (σ : Gal(w.Completion/v.Completion))
    (x : Additive w.Completionˣ) :
    Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion) w.Completionˣ σ x =
      InfinitePlace.unitsRep v w σ x := by sorry
