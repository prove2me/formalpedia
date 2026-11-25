-- Prove2me | Theorems.Thm_GroundTheory_Global_cycHerbrand_gal_completion_units
-- name    : GroundTheory.Global.cycHerbrand_gal_completion_units
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:51:03.813331+00:00
-- url     : https://prove2.me/theorems/4a230f15-d5cc-481c-aa0e-3b4a39218310
-- title:
--   Global: cyc Herbrand gal completion units
-- statement:
--   The Global construction uses the cyc Herbrand gal completion units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrandInfinite.lean#L217-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrandInfinite.lean#L217-L236

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

theorem GroundTheory.Global.cycHerbrand_gal_completion_units (σ : Gal(w.Completion/v.Completion))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    HasHerbrandQuotient
        (cycSubOne (Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion)
          w.Completionˣ) σ)
        (cycNorm (Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion)
          w.Completionˣ)) ∧
      cycHerbrand (Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion)
          w.Completionˣ) σ = Module.finrank v.Completion w.Completion := by sorry
