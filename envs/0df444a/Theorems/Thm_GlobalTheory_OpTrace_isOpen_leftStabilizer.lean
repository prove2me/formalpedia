-- Prove2me | Theorems.Thm_GlobalTheory_OpTrace_isOpen_leftStabilizer
-- name    : GlobalTheory.OpTrace.isOpen_leftStabilizer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:32:11.167717+00:00
-- url     : https://prove2.me/theorems/98d4c183-769e-4cb5-818e-a066d84731cd
-- title:
--   Op Trace: is Open left Stabilizer
-- statement:
--   The Op Trace construction uses the is Open left Stabilizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L676-L693
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/IsHilbertSchmidtOfFiniteDimensional.lean#L676-L693

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHilbertSchmidtOfFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ContinuousLinearMap
open scoped InnerProductSpace Pointwise
noncomputable section
open GlobalTheory GlobalTheory.OpTrace
open GlobalTheory.PRep
variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.OpTrace.isOpen_leftStabilizer [IsTopologicalGroup G] {f : G → ℂ} (hf : IsLocallyConstant f)
    (hc : HasCompactSupport f) : IsOpen (leftStabilizer f : Set G) := by sorry
