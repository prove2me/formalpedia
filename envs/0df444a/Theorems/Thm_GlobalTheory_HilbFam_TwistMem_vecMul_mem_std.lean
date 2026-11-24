-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_TwistMem_vecMul_mem_std
-- name    : GlobalTheory.HilbFam.TwistMem.vecMul_mem_std
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:20:54.976603+00:00
-- url     : https://prove2.me/theorems/534fefdf-db07-47e1-a42d-705617b64759
-- title:
--   Twist Mem: vec Mul mem std
-- statement:
--   The Twist Mem construction uses the vec Mul mem std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemHilbertLatticeTwistIffLift.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemHilbertLatticeTwistIffLift.lean#L16-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasLevelStd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemHilbertLatticeTwistIffLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory GlobalTheory.HilbFam GlobalTheory.HilbFam.TwistMem
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.HilbFam.TwistMem.vecMul_mem_std (B : Matrix (Fin 2) (Fin 2) ℤ) {y : Fin 2 → F} (hy : y ∈ stdLat F) :
    Matrix.vecMul y (B.map (Int.cast : ℤ → F)) ∈ stdLat F := by sorry
