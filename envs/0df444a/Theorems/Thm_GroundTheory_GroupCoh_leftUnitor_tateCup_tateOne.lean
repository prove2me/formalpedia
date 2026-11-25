-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_leftUnitor_tateCup_tateOne
-- name    : GroundTheory.GroupCoh.leftUnitor_tateCup_tateOne
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:50:29.053326+00:00
-- url     : https://prove2.me/theorems/bae18c57-6118-5f05-99e0-1d3475ce0d7f
-- title:
--   Group Coh: left Unitor tate Cup tate One
-- statement:
--   The Group Coh construction uses the left Unitor tate Cup tate One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateCupUnit.lean#L123-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateCupUnit.lean#L123-L129

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupTate
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateCupUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable [Fintype G]

theorem GroundTheory.GroupCoh.leftUnitor_tateCup_tateOne (q : ℤ) (B : Rep.{u} k G) (b : tateCohomology B q) :
    ((tateCohomologyFunctor q).map (λ_ B).hom).hom
        (tateCup 0 q (𝟙_ (Rep.{u} k G)) B q (zero_add _) (tateOne k G) b) = b := by sorry
