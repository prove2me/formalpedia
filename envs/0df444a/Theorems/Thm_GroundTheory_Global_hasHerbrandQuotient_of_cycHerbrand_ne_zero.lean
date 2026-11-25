-- Prove2me | Theorems.Thm_GroundTheory_Global_hasHerbrandQuotient_of_cycHerbrand_ne_zero
-- name    : GroundTheory.Global.hasHerbrandQuotient_of_cycHerbrand_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T07:49:34.461803+00:00
-- url     : https://prove2.me/theorems/f961635b-5ff7-54ae-8cb8-0e1382e87e73
-- title:
--   Global: has Herbrand Quotient of cyc Herbrand ne zero
-- statement:
--   The Global construction uses the has Herbrand Quotient of cyc Herbrand ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrandInfinite.lean#L17-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/LocalHerbrandInfinite.lean#L17-L22

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
variable {k G V : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]

theorem GroundTheory.Global.hasHerbrandQuotient_of_cycHerbrand_ne_zero {ρ : Representation k G V} {σ : G}
    (h : cycHerbrand ρ σ ≠ 0) : HasHerbrandQuotient (cycSubOne ρ σ) (cycNorm ρ) := by sorry
