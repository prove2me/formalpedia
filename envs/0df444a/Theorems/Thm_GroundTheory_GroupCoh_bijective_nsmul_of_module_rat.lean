-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_bijective_nsmul_of_module_rat
-- name    : GroundTheory.GroupCoh.bijective_nsmul_of_module_rat
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:36:50.353324+00:00
-- url     : https://prove2.me/theorems/9e4b1530-893e-4573-9b24-c39b1c76bf4a
-- title:
--   Group Coh: bijective nsmul of module rat
-- statement:
--   The Group Coh construction uses the bijective nsmul of module rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/UniquelyDivisible.lean#L50-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/UniquelyDivisible.lean#L50-L58

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
universe u
variable {G : Type} [Group G] [Fintype G]

theorem GroundTheory.GroupCoh.bijective_nsmul_of_module_rat {V : Type*} [AddCommGroup V] [Module ℚ V] {n : ℕ}
    (hn : n ≠ 0) : Function.Bijective fun v : V => n • v := by sorry
