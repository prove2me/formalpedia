-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateLeftIso_hom
-- name    : GroundTheory.GroupCoh.tateLeftIso_hom
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:06:29.461802+00:00
-- url     : https://prove2.me/theorems/4559143b-998c-418d-a755-68840ccdf5ab
-- title:
--   Group Coh: tate Left Iso hom
-- statement:
--   The Group Coh construction uses the tate Left Iso hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L114-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateShift.lean#L114-L115

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateLow
import Definitions.Def_GroundTheory_TateCohomology_CupTateShift
import Theorems.Thm_GroundTheory_GroupCoh_augSES_tensorRight_shortExact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable [Fintype G]

theorem GroundTheory.GroupCoh.tateLeftIso_hom (A B : Rep.{u} k G) (r : ℤ) :
    (tateLeftIso A B r).hom = tδ (augSES_tensorRight_shortExact A B) r (r + 1) rfl := by sorry
