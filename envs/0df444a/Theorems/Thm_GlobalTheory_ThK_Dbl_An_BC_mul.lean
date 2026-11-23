-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_An_BC_mul
-- name    : GlobalTheory.ThK.Dbl.An.BC.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:37:09.448798+00:00
-- url     : https://prove2.me/theorems/b7cc4dda-72e3-43fa-9723-8a738c53cc46
-- title:
--   BC: mul
-- statement:
--   The BC construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/FarRight.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/FarRight.lean#L15-L19

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

theorem GlobalTheory.ThK.Dbl.An.BC.mul (h : BC f) (h' : BC g) : BC fun x => f x * g x := by sorry
