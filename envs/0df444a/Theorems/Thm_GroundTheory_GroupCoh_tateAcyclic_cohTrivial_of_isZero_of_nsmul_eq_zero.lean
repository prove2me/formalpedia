-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateAcyclic_cohTrivial_of_isZero_of_nsmul_eq_zero
-- name    : GroundTheory.GroupCoh.tateAcyclic_cohTrivial_of_isZero_of_nsmul_eq_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:15:27.655122+00:00
-- url     : https://prove2.me/theorems/c5bc0c41-88b2-5560-845a-9000a5f33791
-- title:
--   Group Coh: tate Acyclic coh Trivial of is Zero of nsmul eq zero
-- statement:
--   The Group Coh construction uses the tate Acyclic coh Trivial of is Zero of nsmul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupCohTrivialInt.lean#L140-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/PGroupCohTrivialInt.lean#L140-L145

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
variable {G : Type} [Group G] (p : ℕ) [Fact p.Prime]
variable [Fintype G]

theorem GroundTheory.GroupCoh.tateAcyclic_cohTrivial_of_isZero_of_nsmul_eq_zero {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p G) (M : Rep ℤ G) (hM : ∀ x : M, p • x = 0) (q : ℤ)
    (hq : IsZero (tateCohomology M q)) : TateAcyclic M ∧ CohTrivial M := by sorry
