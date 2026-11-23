-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_hasDerivAt_line
-- name    : GlobalTheory.Mem.Lift.DCalc.hasDerivAt_line
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:12.195038+00:00
-- url     : https://prove2.me/theorems/92d48a0e-8ff7-4997-ac82-af36a5f52e2b
-- title:
--   DCalc: has Deriv At line
-- statement:
--   The DCalc construction uses the has Deriv At line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HeisenbergSmoothVectorDerivativeCalculus.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HeisenbergSmoothVectorDerivativeCalculus.lean#L11-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsQuadOfPlane
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_HeisenbergSmoothVectorDerivativeCalculus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Lift GlobalTheory.Mem.Lift.DCalc
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]

theorem GlobalTheory.Mem.Lift.DCalc.hasDerivAt_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : V → E} (hF : Differentiable ℝ F)
    (w y : V) : HasDerivAt (fun t : ℝ => F (w + t • y)) (fderiv ℝ F w y) 0 := by sorry
