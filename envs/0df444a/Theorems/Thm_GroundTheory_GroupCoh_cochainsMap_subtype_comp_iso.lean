-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_cochainsMap_subtype_comp_iso
-- name    : GroundTheory.GroupCoh.cochainsMap_subtype_comp_iso
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:35:31.512602+00:00
-- url     : https://prove2.me/theorems/7936f045-b1e5-47d0-9661-104930bf890d
-- title:
--   Group Coh: cochains Map subtype comp iso
-- statement:
--   The Group Coh construction uses the cochains Map subtype comp iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresPos.lean#L115-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/ResCoresPos.lean#L115-L120

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_ResCoresPos
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
open CategoryTheory Limits Rep groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] (S : Subgroup G)
set_option backward.isDefEq.respectTransparency false

theorem GroundTheory.GroupCoh.cochainsMap_subtype_comp_iso (A : Rep.{u} k G) :
    cochainsMap S.subtype (𝟙 (res S.subtype A)) ≫ (inhomogeneousCochainsIso (res S.subtype A)).hom =
      (inhomogeneousCochainsIso A).hom ≫ resHomComplex S A ≫
        linearYonedaObjMap (barIncl (k := k) S) (res S.subtype A) := by sorry
