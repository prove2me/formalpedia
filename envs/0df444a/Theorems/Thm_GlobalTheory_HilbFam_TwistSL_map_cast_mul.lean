-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_TwistSL_map_cast_mul
-- name    : GlobalTheory.HilbFam.TwistSL.map_cast_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:20:41.233437+00:00
-- url     : https://prove2.me/theorems/a68c44bd-0559-4b0e-a00d-14348291e804
-- title:
--   Twist SL: map cast mul
-- statement:
--   The Twist SL construction uses the map cast mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertLatticeTwistByMatrixModNMulSL2Z.lean#L24-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HilbertLatticeTwistByMatrixModNMulSL2Z.lean#L24-L26

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

theorem GlobalTheory.HilbFam.TwistSL.map_cast_mul (R : Type) [CommRing R] (A B : Matrix (Fin 2) (Fin 2) ℤ) :
    (A * B).map (Int.cast : ℤ → R) = A.map (Int.cast : ℤ → R) * B.map (Int.cast : ℤ → R) := by sorry
