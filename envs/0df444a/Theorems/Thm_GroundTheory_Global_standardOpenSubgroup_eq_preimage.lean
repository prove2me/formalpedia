-- Prove2me | Theorems.Thm_GroundTheory_Global_standardOpenSubgroup_eq_preimage
-- name    : GroundTheory.Global.standardOpenSubgroup_eq_preimage
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:59:02.054715+00:00
-- url     : https://prove2.me/theorems/7205d905-2e2a-4d20-b497-b0ddf6dd04ff
-- title:
--   Global: standard Open Subgroup eq preimage
-- statement:
--   The Global construction uses the standard Open Subgroup eq preimage property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasure.lean#L484-L490
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasure.lean#L484-L490

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_NormOneCompact
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_StandardOpenEquiv
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasurable
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter MeasureTheory TopologicalSpace
open scoped NumberField.AdeleRing RestrictedProduct ENNReal NNReal
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.standardOpenSubgroup_eq_preimage :
    (IdeleGroup.standardOpenSubgroup K : Set (IdeleGroup K)) =
      IdeleGroup.prodEquiv K ⁻¹' (Set.univ ×ˢ (finiteIntegralUnits K : Set _)) := by sorry
