-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_card_smul_tateCohomology
-- name    : GroundTheory.GroupCoh.card_smul_tateCohomology
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:19:41.372112+00:00
-- url     : https://prove2.me/theorems/46bb0c55-dc3c-47c5-adcf-1b3c016433ac
-- title:
--   Group Coh: card smul tate Cohomology
-- statement:
--   The Group Coh construction uses the card smul tate Cohomology property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/Annihilation.lean#L47-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/Annihilation.lean#L47-L55

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_Annihilation
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
variable {R G : Type u} [CommRing R] [Group G] [Fintype G]

theorem GroundTheory.GroupCoh.card_smul_tateCohomology (A : Rep.{u} R G) (n : ℤ) (x : tateCohomology A n) :
    Fintype.card G • x = 0 := by sorry
