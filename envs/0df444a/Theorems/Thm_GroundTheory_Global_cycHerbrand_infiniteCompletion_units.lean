-- Prove2me | Theorems.Thm_GroundTheory_Global_cycHerbrand_infiniteCompletion_units
-- name    : GroundTheory.Global.cycHerbrand_infiniteCompletion_units
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:57:06.090886+00:00
-- url     : https://prove2.me/theorems/b2e9e2a3-1f41-5ae4-a405-dfbb39d0118d
-- title:
--   Global: cyc Herbrand infinite Completion units
-- statement:
--   The Global construction uses the cyc Herbrand infinite Completion units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrandInfinite.lean#L249-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrandInfinite.lean#L249-L265

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

theorem GroundTheory.Global.cycHerbrand_infiniteCompletion_units [Fintype (MulAction.stabilizer Gal(L/K) w)]
    (τ : MulAction.stabilizer Gal(L/K) w) (hτ : ∀ σ, σ ∈ Subgroup.zpowers τ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w)
          w.Completionˣ) τ)
        (cycNorm (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w)
          w.Completionˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction (MulAction.stabilizer Gal(L/K) w)
          w.Completionˣ) τ = Module.finrank v.Completion w.Completion := by sorry
