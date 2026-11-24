-- Prove2me | Theorems.Thm_GlobalTheory_densHom_scale
-- name    : GlobalTheory.densHom_scale
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:34:07.157641+00:00
-- url     : https://prove2.me/theorems/80db9e7c-c554-4e8f-83e8-df97e6a8437c
-- title:
--   Global Theory: dens Hom scale
-- statement:
--   The Global Theory construction uses the dens Hom scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsDensityOriginOfAlmostHomogeneous.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsDensityOriginOfAlmostHomogeneous.lean#L14-L19

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataCD
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsDensityOriginOfAlmostHomogeneous
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open GlobalTheory
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
open MeasureTheory Filter Topology Matrix
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem GlobalTheory.densHom_scale (l : Measure V) [l.IsAddHaarMeasure] (x : V) {s r : ℝ}
    (hs : 0 < s) (hr : 0 < r) :
    l (Metric.closedBall x (s * r)) =
      ENNReal.ofReal (s ^ Module.finrank ℝ V) * l (Metric.ball 0 r) := by sorry
