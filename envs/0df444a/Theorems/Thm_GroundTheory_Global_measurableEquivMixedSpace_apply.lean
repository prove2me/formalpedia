-- Prove2me | Theorems.Thm_GroundTheory_Global_measurableEquivMixedSpace_apply
-- name    : GroundTheory.Global.measurableEquivMixedSpace_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:56:28.129951+00:00
-- url     : https://prove2.me/theorems/a53f2ee6-a73d-5079-b8e8-c2107220f153
-- title:
--   Global: measurable Equiv Mixed Space apply
-- statement:
--   The Global construction uses the measurable Equiv Mixed Space apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleMeasure.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleMeasure.lean#L69-L71

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Adele_Compact
import Definitions.Def_GroundTheory_GlobalFields_Adele_Discrete
import Definitions.Def_GroundTheory_GlobalFields_Adele_Topology
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasurable
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
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
open NumberField NumberField.mixedEmbedding IsDedekindDomain MeasureTheory Measure
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Global.measurableEquivMixedSpace_apply (x : InfiniteAdeleRing K) :
    measurableEquivMixedSpace K x = homeomorphMixedSpace K x := by sorry
