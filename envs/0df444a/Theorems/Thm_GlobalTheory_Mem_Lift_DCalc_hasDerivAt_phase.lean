-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_hasDerivAt_phase
-- name    : GlobalTheory.Mem.Lift.DCalc.hasDerivAt_phase
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:57.608734+00:00
-- url     : https://prove2.me/theorems/3682f46a-3f07-432b-8ee7-ede8b60b0090
-- title:
--   DCalc: has Deriv At phase
-- statement:
--   The DCalc construction uses the has Deriv At phase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HeisenbergSmoothVectorDerivativeCalculus.lean#L24-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HeisenbergSmoothVectorDerivativeCalculus.lean#L24-L29

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

theorem GlobalTheory.Mem.Lift.DCalc.hasDerivAt_phase (a : ℝ) {G : ℝ → B} {G' : B} (hG : HasDerivAt G G' 0) :
    HasDerivAt (fun t : ℝ => cexp (π * I * ((t * a : ℝ) : ℂ)) • G t) (G' + (π * I * a : ℂ) • G 0) 0 := by sorry
