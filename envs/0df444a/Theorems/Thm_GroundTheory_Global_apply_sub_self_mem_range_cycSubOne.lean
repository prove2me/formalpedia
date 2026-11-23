-- Prove2me | Theorems.Thm_GroundTheory_Global_apply_sub_self_mem_range_cycSubOne
-- name    : GroundTheory.Global.apply_sub_self_mem_range_cycSubOne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:23:48.947797+00:00
-- url     : https://prove2.me/theorems/14d23037-beef-4f16-8bd9-85a703a3a029
-- title:
--   Global: apply sub self mem range cyc Sub One
-- statement:
--   The Global construction uses the apply sub self mem range cyc Sub One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTate.lean#L124-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTate.lean#L124-L144

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

theorem GroundTheory.Global.apply_sub_self_mem_range_cycSubOne (ρ : Representation k G V) {σ : G}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (g : G) (x : V) :
    ρ g x - x ∈ (cycSubOne ρ σ).range := by sorry
