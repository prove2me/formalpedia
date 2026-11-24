-- Prove2me | Theorems.Thm_GroundTheory_Global_range_cycSubOne_eq_closure
-- name    : GroundTheory.Global.range_cycSubOne_eq_closure
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:42:41.893091+00:00
-- url     : https://prove2.me/theorems/b33de99e-ec94-485c-baa5-fd45a65aa2f4
-- title:
--   Global: range cyc Sub One eq closure
-- statement:
--   The Global construction uses the range cyc Sub One eq closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTate.lean#L146-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTate.lean#L146-L154

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

theorem GroundTheory.Global.range_cycSubOne_eq_closure (ρ : Representation k G V) {σ : G}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (cycSubOne ρ σ).range = AddSubgroup.closure {y | ∃ g x, ρ g x - x = y} := by sorry
