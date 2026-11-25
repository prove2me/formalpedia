-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_indResAdjunction_counit_app_hom_mk
-- name    : GroundTheory.GroupCoh.indResAdjunction_counit_app_hom_mk
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:29:05.524085+00:00
-- url     : https://prove2.me/theorems/95f0714e-430c-4a7c-aa01-b5d11877b784
-- title:
--   Group Coh: ind Res Adjunction counit app hom mk
-- statement:
--   The Group Coh construction uses the ind Res Adjunction counit app hom mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CoresRes.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/CoresRes.lean#L32-L36

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
omit [S.FiniteIndex] [DecidableRel (QuotientGroup.rightRel S)]

theorem GroundTheory.GroupCoh.indResAdjunction_counit_app_hom_mk (A : Rep.{u} k G) (g : G) (a : A) :
    ((indResAdjunction k S.subtype).counit.app A).hom
      (Representation.IndV.mk S.subtype (res S.subtype A).ρ g a) = A.ρ g⁻¹ a := by sorry
