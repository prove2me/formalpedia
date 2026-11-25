-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_isOpen_positiveAt
-- name    : GroundTheory.Global.IdeleGroup.isOpen_positiveAt
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T08:11:55.560556+00:00
-- url     : https://prove2.me/theorems/52bc4aa6-c6e4-5d71-a739-b0a788ea8a63
-- title:
--   Idele Group: is Open positive At
-- statement:
--   The Idele Group construction uses the is Open positive At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/CongruenceSubgroupLeStandardOpenSubgroup.lean#L40-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ClassFieldConsequences/CongruenceSubgroupLeStandardOpenSubgroup.lean#L40-L50

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain WithZero Function
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
open GroundTheory.Global.IdeleGroup

theorem GroundTheory.Global.IdeleGroup.isOpen_positiveAt (S : Set {w : InfinitePlace K // w.IsReal}) :
    IsOpen (positiveAt S : Set (IdeleGroup K)) := by sorry
