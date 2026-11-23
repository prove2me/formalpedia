-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_An_BC_int
-- name    : GlobalTheory.ThK.Dbl.An.BC.int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:13.850998+00:00
-- url     : https://prove2.me/theorems/68c5a66a-ffbd-4731-9eef-ecd28503724b
-- title:
--   BC: int
-- statement:
--   The BC construction uses the int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/FarRight.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/FarRight.lean#L25-L26

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_FarRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.An
open MeasureTheory Filter Topology
variable {X X' : Type} [TopologicalSpace X] [TopologicalSpace X'] {f g : X → ℂ}

theorem GlobalTheory.ThK.Dbl.An.BC.int [MeasurableSpace X] [OpensMeasurableSpace X] (h : BC f) (μ : Measure X) [IsFiniteMeasure μ] : Integrable f μ := by sorry
