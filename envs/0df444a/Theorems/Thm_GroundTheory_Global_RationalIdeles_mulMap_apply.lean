-- Prove2me | Theorems.Thm_GroundTheory_Global_RationalIdeles_mulMap_apply
-- name    : GroundTheory.Global.RationalIdeles.mulMap_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:55:12.328995+00:00
-- url     : https://prove2.me/theorems/da13c947-da41-5fbf-bf59-aed18ce6e5ee
-- title:
--   Rational Ideles: mul Map apply
-- statement:
--   The Rational Ideles construction uses the mul Map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/Rational.lean#L236-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/Rational.lean#L236-L238

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_StandardOpenEquiv
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_Rational
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Topology
open scoped NumberField.AdeleRing
noncomputable section
attribute [local instance] GroundTheory.Global._p2m_local_instance_d54fe1196b_11
open GroundTheory.Global.RationalIdeles
open IdeleGroup

theorem GroundTheory.Global.RationalIdeles.mulMap_apply (p : ℚˣ × positiveSubgroup) :
    mulMap p = diagonal ℚ p.1 * (p.2 : IdeleGroup ℚ) := by sorry
