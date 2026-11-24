-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_TwistSL_vecMul_mem_stdLat
-- name    : GlobalTheory.HilbFam.TwistSL.vecMul_mem_stdLat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:20:55.240979+00:00
-- url     : https://prove2.me/theorems/35b317ca-fb87-4859-835e-e1b2762ed692
-- title:
--   Twist SL: vec Mul mem std Lat
-- statement:
--   The Twist SL construction uses the vec Mul mem std Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertLatticeTwistByMatrixModNMulSL2Z.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertLatticeTwistByMatrixModNMulSL2Z.lean#L13-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemHilbertLatticeTwistIffLiftStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HilbertLatticeTwistByMatrixModNMulSL2Z
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam GlobalTheory.HilbFam.TwistSL

theorem GlobalTheory.HilbFam.TwistSL.vecMul_mem_stdLat {F : Type} [Field F] [NumberField F] (B : Matrix (Fin 2) (Fin 2) ℤ) {w : Fin 2 → F}
    (hw : w ∈ stdLat F) : Matrix.vecMul w (B.map (Int.cast : ℤ → F)) ∈ stdLat F := by sorry
