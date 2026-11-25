-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_isZero_tateCohomology_of_nsmul_injective
-- name    : GroundTheory.GroupCoh.isZero_tateCohomology_of_nsmul_injective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:16:17.383573+00:00
-- url     : https://prove2.me/theorems/c91460e9-dd5a-4afc-9692-4138a4fa39c6
-- title:
--   Group Coh: is Zero tate Cohomology of nsmul injective
-- statement:
--   The Group Coh construction uses the is Zero tate Cohomology of nsmul injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CohTrivialPGroup.lean#L26-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CohTrivialPGroup.lean#L26-L47

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
variable {G : Type} [Group G] [Fintype G] {p : ℕ} [Fact p.Prime]

theorem GroundTheory.GroupCoh.isZero_tateCohomology_of_nsmul_injective {H : Type} [Group H] [Fintype H]
    (hH : IsPGroup p H) (A : Rep ℤ H) (n : ℤ)
    (hinj : Function.Injective fun x : tateCohomology A n => p • x) :
    IsZero (tateCohomology A n) := by sorry
