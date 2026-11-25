-- Prove2me | Theorems.Thm_GroundTheory_Global_RationalIdeles_ideleClassGroupEquiv_mk
-- name    : GroundTheory.Global.RationalIdeles.ideleClassGroupEquiv_mk
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:00:58.29295+00:00
-- url     : https://prove2.me/theorems/71ea841c-9f8c-479c-ad56-52c3948c547e
-- title:
--   Rational Ideles: idele Class Group Equiv mk
-- statement:
--   The Rational Ideles construction uses the idele Class Group Equiv mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/Rational.lean#L269-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/Rational.lean#L269-L275

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

theorem GroundTheory.Global.RationalIdeles.ideleClassGroupEquiv_mk (x : positiveSubgroup) :
    ideleClassGroupEquiv (IdeleClassGroup.mk ℚ x) =
      (⟨realPart x, (Units.mem_posSubgroup _).2 (mem_positiveSubgroup.1 x.2).2⟩,
        integerUnitsEquiv (positiveSubgroupEquiv x).2) := by sorry
