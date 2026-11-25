-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_unit_comp_indCoindIso_inv_comp_counit
-- name    : GroundTheory.GroupCoh.unit_comp_indCoindIso_inv_comp_counit
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:35:08.442975+00:00
-- url     : https://prove2.me/theorems/4ed25195-db69-5cd8-b99f-0e7502888f6d
-- title:
--   Group Coh: unit comp ind Coind Iso inv comp counit
-- statement:
--   The Group Coh construction uses the unit comp ind Coind Iso inv comp counit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CoresRes.lean#L38-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CoresRes.lean#L38-L56

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_ResCores
import Definitions.Def_GroundTheory_TateCohomology_CoresRes
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
variable {k G : Type u} [CommRing k] [Group G]
variable (S : Subgroup G) [S.FiniteIndex] [DecidableRel (QuotientGroup.rightRel S)]
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem GroundTheory.GroupCoh.unit_comp_indCoindIso_inv_comp_counit (A : Rep.{u} k G) :
    (resCoindAdjunction.{u, u} k S.subtype).unit.app A ≫ (indCoindIso (res S.subtype A)).inv ≫
      (indResAdjunction.{u} k S.subtype).counit.app A = S.index • 𝟙 A := by sorry
