-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_nsmul_eq_zero_coind
-- name    : GroundTheory.GroupCoh.nsmul_eq_zero_coind
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:33:04.642852+00:00
-- url     : https://prove2.me/theorems/f4b5ac07-8afb-419f-9a35-106b968c7e94
-- title:
--   Group Coh: nsmul eq zero coind
-- statement:
--   The Group Coh construction uses the nsmul eq zero coind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupCohTrivialInt.lean#L88-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupCohTrivialInt.lean#L88-L90

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

theorem GroundTheory.GroupCoh.nsmul_eq_zero_coind (M : Rep.{u} k G) {n : ℕ} (hM : ∀ x : M, n • x = 0)
    (x : coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype M)) : n • x = 0 := by sorry
