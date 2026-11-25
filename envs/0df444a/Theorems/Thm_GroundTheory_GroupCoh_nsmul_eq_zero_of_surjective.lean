-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_nsmul_eq_zero_of_surjective
-- name    : GroundTheory.GroupCoh.nsmul_eq_zero_of_surjective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:12.042091+00:00
-- url     : https://prove2.me/theorems/3b4d9c5a-04f4-5184-916d-00603afe2f46
-- title:
--   Group Coh: nsmul eq zero of surjective
-- statement:
--   The Group Coh construction uses the nsmul eq zero of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupCohTrivialInt.lean#L75-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupCohTrivialInt.lean#L75-L79

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

theorem GroundTheory.GroupCoh.nsmul_eq_zero_of_surjective {A B : Rep.{u} k G} (f : A ⟶ B)
    (hf : Function.Surjective f.hom) {n : ℕ} (hA : ∀ x : A, n • x = 0) (y : B) : n • y = 0 := by sorry
