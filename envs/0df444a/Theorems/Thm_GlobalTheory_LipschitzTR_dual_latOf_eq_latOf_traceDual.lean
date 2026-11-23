-- Prove2me | Theorems.Thm_GlobalTheory_LipschitzTR_dual_latOf_eq_latOf_traceDual
-- name    : GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:47.160786+00:00
-- url     : https://prove2.me/theorems/45cc1dba-d396-4c85-a1b7-2135ea599cb3
-- title:
--   Lipschitz TR: dual lat Of eq lat Of trace Dual
-- statement:
--   The Lipschitz TR construction uses the dual lat Of eq lat Of trace Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualLatticeImageEqLatticeImageTraceDual.lean#L88-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualLatticeImageEqLatticeImageTraceDual.lean#L88-L106

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

theorem GlobalTheory.LipschitzTR.dual_latOf_eq_latOf_traceDual (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0) :
    Formalism.H.dual (latOf N) = latOf (FractionalIdeal.dual ℤ ℚ N) := by sorry
