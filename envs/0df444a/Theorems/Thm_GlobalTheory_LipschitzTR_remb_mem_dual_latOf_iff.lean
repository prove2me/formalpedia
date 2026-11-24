-- Prove2me | Theorems.Thm_GlobalTheory_LipschitzTR_remb_mem_dual_latOf_iff
-- name    : GlobalTheory.LipschitzTR.remb_mem_dual_latOf_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:12:36.818251+00:00
-- url     : https://prove2.me/theorems/f5138a3d-3b2f-46cd-89e1-c1a65d88f9d8
-- title:
--   Lipschitz TR: remb mem dual lat Of iff
-- statement:
--   The Lipschitz TR construction uses the remb mem dual lat Of iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualLatticeImageEqLatticeImageTraceDual.lean#L22-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DualLatticeImageEqLatticeImageTraceDual.lean#L22-L42

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

theorem GlobalTheory.LipschitzTR.remb_mem_dual_latOf_iff (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0) (ν : F) :
    remb F ν ∈ Formalism.H.dual (latOf N) ↔ ν ∈ FractionalIdeal.dual ℤ ℚ N := by sorry
