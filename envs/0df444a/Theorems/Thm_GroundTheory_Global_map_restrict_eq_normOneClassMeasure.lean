-- Prove2me | Theorems.Thm_GroundTheory_Global_map_restrict_eq_normOneClassMeasure
-- name    : GroundTheory.Global.map_restrict_eq_normOneClassMeasure
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:11:44.399351+00:00
-- url     : https://prove2.me/theorems/bcd6628f-ecf8-5195-8a3d-34f8f8cbcc6f
-- title:
--   Global: map restrict eq norm One Class Measure
-- statement:
--   The Global construction uses the map restrict eq norm One Class Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureQuotient.lean#L252-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/IdeleMeasureQuotient.lean#L252-L255

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureNormOne
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureCosets
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_NormOneCompact
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasureQuotient
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
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise
open GroundTheory GroundTheory.Global
noncomputable section
open IdeleGroup
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.map_restrict_eq_normOneClassMeasure {F : Set (normOneSubgroup K)}
    (hF : IsFundamentalDomain (diagonalNormOne K).op F (normOneMeasure K)) :
    Measure.map QuotientGroup.mk ((normOneMeasure K).restrict F) = normOneClassMeasure K := by sorry
