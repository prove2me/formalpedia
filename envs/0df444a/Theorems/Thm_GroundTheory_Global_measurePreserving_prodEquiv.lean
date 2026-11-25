-- Prove2me | Theorems.Thm_GroundTheory_Global_measurePreserving_prodEquiv
-- name    : GroundTheory.Global.measurePreserving_prodEquiv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:14:52.346224+00:00
-- url     : https://prove2.me/theorems/cbdcf513-fc86-5f36-9c71-2633de1d59e4
-- title:
--   Global: measure Preserving prod Equiv
-- statement:
--   The Global construction uses the measure Preserving prod Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasure.lean#L460-L469
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasure.lean#L460-L469

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

theorem GroundTheory.Global.measurePreserving_prodEquiv :
    MeasurePreserving (IdeleGroup.prodEquiv K) (ideleMeasure K)
      ((infiniteIdeleMeasure K).prod (finiteIdeleMeasure K)) := by sorry
