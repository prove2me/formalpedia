-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateIsoH_map_apply
-- name    : GroundTheory.GroupCoh.tateIsoH_map_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:51:56.657184+00:00
-- url     : https://prove2.me/theorems/d5d4760a-936a-435c-a92a-44bed1b3fb85
-- title:
--   Group Coh: tate Iso H map apply
-- statement:
--   The Group Coh construction uses the tate Iso H map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateNatural.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CupTateNatural.lean#L91-L95

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupTate
import Definitions.Def_GroundTheory_TateCohomology_CupTateNatural
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
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem GroundTheory.GroupCoh.tateIsoH_map_apply {X Y : Rep.{u} k G} (φ : X ⟶ Y) (n : ℕ) [NeZero n]
    (x : tateCohomology X n) :
    (tateIsoH Y n n rfl).hom.hom (((tateCohomologyFunctor n).map φ).hom x) =
      groupCohomology.map (MonoidHom.id G) φ n ((tateIsoH X n n rfl).hom.hom x) := by sorry
