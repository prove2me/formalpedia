-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_hom_nsmul_apply
-- name    : GroundTheory.GroupCoh.hom_nsmul_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:40:56.361619+00:00
-- url     : https://prove2.me/theorems/5ce949f0-a71e-58c1-8abf-46c976764116
-- title:
--   Group Coh: hom nsmul apply
-- statement:
--   The Group Coh construction uses the hom nsmul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CohTrivialPGroup.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CohTrivialPGroup.lean#L16-L17

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivialInt
import Definitions.Def_GroundTheory_TateCohomology_Annihilation
import Definitions.Def_GroundTheory_TateCohomology_CohTrivialPGroup
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
variable {k H : Type u} [CommRing k] [Group H] {A B : Rep.{u} k H}

theorem GroundTheory.GroupCoh.hom_nsmul_apply (f : A ⟶ B) (n : ℕ) (x : A) : f.hom (n • x) = n • f.hom x := by sorry
