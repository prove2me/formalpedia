-- Prove2me | Theorems.Thm_GroundTheory_Global_RationalIdeles_realEquiv_apply
-- name    : GroundTheory.Global.RationalIdeles.realEquiv_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:00:44.929824+00:00
-- url     : https://prove2.me/theorems/bb6130c9-00a5-48a8-bfff-de93d674c0de
-- title:
--   Rational Ideles: real Equiv apply
-- statement:
--   The Rational Ideles construction uses the real Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/Rational.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/IdeleGroups/Rational.lean#L25-L28

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

theorem GroundTheory.Global.RationalIdeles.realEquiv_apply (x : InfiniteAdeleRing ℚ) :
    realEquiv x = InfinitePlace.Completion.extensionEmbeddingOfIsReal
      (isReal_infinitePlace default) (x default) := by sorry
