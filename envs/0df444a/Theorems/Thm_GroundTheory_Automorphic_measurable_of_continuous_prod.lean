-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_measurable_of_continuous_prod
-- name    : GroundTheory.Automorphic.measurable_of_continuous_prod
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:35:48.084737+00:00
-- url     : https://prove2.me/theorems/fb87b4d3-9ab8-4ae4-a1c5-de4ddfe440f4
-- title:
--   Automorphic: measurable of continuous prod
-- statement:
--   The Automorphic construction uses the measurable of continuous prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FinePartition.lean#L164-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/FinePartition.lean#L164-L218

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FinePartition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology Uniformity UniformSpace Function
open MeasurablePartition
variable {X Y : Type*} [UniformSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [UniformSpace Y] [CompactSpace Y] [MeasurableSpace Y]
  [OpensMeasurableSpace Y]

theorem GroundTheory.Automorphic.measurable_of_continuous_prod {β : Type*} [PseudoMetricSpace β] [MeasurableSpace β]
    [BorelSpace β] {k : X × Y → β} (hk : Continuous k) : Measurable k := by sorry
