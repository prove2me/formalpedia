-- Prove2me | Theorems.Thm_GlobalTheory_LipschitzTR_inner_remb_eq_trace
-- name    : GlobalTheory.LipschitzTR.inner_remb_eq_trace
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:45.332391+00:00
-- url     : https://prove2.me/theorems/ca77c7e4-6fe7-4b95-b88a-4a036834605d
-- title:
--   Lipschitz TR: inner remb eq trace
-- statement:
--   The Lipschitz TR construction uses the inner remb eq trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualLatticeImageEqLatticeImageTraceDual.lean#L16-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualLatticeImageEqLatticeImageTraceDual.lean#L16-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualLatticeImageEqLatticeImageTraceDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.LipschitzTR
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem GlobalTheory.LipschitzTR.inner_remb_eq_trace (a b : F) :
    ⟪remb F a, remb F b⟫ = ((Algebra.trace ℚ F (a * b) : ℚ) : ℝ) := by sorry
