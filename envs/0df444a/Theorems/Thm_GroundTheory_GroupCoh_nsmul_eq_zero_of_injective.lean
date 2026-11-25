-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_nsmul_eq_zero_of_injective
-- name    : GroundTheory.GroupCoh.nsmul_eq_zero_of_injective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:15:35.527116+00:00
-- url     : https://prove2.me/theorems/0d1f029e-c60f-583c-ad20-1173f8270195
-- title:
--   Group Coh: nsmul eq zero of injective
-- statement:
--   The Group Coh construction uses the nsmul eq zero of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupCohTrivialInt.lean#L81-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupCohTrivialInt.lean#L81-L86

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivial
import Definitions.Def_GroundTheory_TateCohomology_TateAddEquivAbelianizationTateClass
import Definitions.Def_GroundTheory_TateCohomology_PGroupCohTrivialInt
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
open CategoryTheory Limits Rep groupHomology
universe u
variable {k G : Type u} [CommRing k] [Group G]

theorem GroundTheory.GroupCoh.nsmul_eq_zero_of_injective {A B : Rep.{u} k G} (f : A ⟶ B)
    (hf : Function.Injective f.hom) {n : ℕ} (hB : ∀ y : B, n • y = 0) (x : A) : n • x = 0 := by sorry
