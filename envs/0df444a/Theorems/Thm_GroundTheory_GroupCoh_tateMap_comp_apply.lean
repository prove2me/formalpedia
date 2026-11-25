-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_tateMap_comp_apply
-- name    : GroundTheory.GroupCoh.tateMap_comp_apply
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:14:47.06445+00:00
-- url     : https://prove2.me/theorems/2c6dddec-7abb-46dd-96c5-f4b81266dc72
-- title:
--   Group Coh: tate Map comp apply
-- statement:
--   The Group Coh construction uses the tate Map comp apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateConnecting.lean#L133-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/TateConnecting.lean#L133-L139

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupConnecting
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory groupCohomology
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
variable {X Y Z : Rep k G}

theorem GroundTheory.GroupCoh.tateMap_comp_apply (φ : X ⟶ Y) (ψ : Y ⟶ Z) (i : ℤ) (x : (tateComplex X).X i) :
    ((tateComplex.map (φ ≫ ψ)).f i).hom x =
      ((tateComplex.map ψ).f i).hom (((tateComplex.map φ).f i).hom x) := by sorry
