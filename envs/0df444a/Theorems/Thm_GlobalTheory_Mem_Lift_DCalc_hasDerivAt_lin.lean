-- Prove2me | Theorems.Thm_GlobalTheory_Mem_Lift_DCalc_hasDerivAt_lin
-- name    : GlobalTheory.Mem.Lift.DCalc.hasDerivAt_lin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:35:39.563364+00:00
-- url     : https://prove2.me/theorems/aa22b4f6-f38a-4f83-8dbb-70fdeeac5e0d
-- title:
--   DCalc: has Deriv At lin
-- statement:
--   The DCalc construction uses the has Deriv At lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HeisenbergSmoothVectorDerivativeCalculus.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/HeisenbergSmoothVectorDerivativeCalculus.lean#L19-L22

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

theorem GlobalTheory.Mem.Lift.DCalc.hasDerivAt_lin (a : ℝ) : HasDerivAt (fun t : ℝ => (π * I * ((t * a : ℝ) : ℂ))) (π * I * a) 0 := by sorry
