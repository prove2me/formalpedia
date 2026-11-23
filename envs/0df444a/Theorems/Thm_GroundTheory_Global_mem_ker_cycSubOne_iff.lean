-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_ker_cycSubOne_iff
-- name    : GroundTheory.Global.mem_ker_cycSubOne_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:31.387627+00:00
-- url     : https://prove2.me/theorems/79c180e3-56ac-4c25-90aa-c35d010d008e
-- title:
--   Global: mem ker cyc Sub One iff
-- statement:
--   The Global construction uses the mem ker cyc Sub One iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTate.lean#L118-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTate.lean#L118-L122

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

theorem GroundTheory.Global.mem_ker_cycSubOne_iff (ρ : Representation k G V) {σ : G}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (x : V) :
    x ∈ (cycSubOne ρ σ).ker ↔ ∀ g, ρ g x = x := by sorry
