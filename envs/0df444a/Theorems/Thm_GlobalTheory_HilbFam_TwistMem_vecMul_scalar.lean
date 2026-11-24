-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_TwistMem_vecMul_scalar
-- name    : GlobalTheory.HilbFam.TwistMem.vecMul_scalar
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T14:20:54.336998+00:00
-- url     : https://prove2.me/theorems/f6e5ad41-da13-4dc8-968d-4c8f95c6dc97
-- title:
--   Twist Mem: vec Mul scalar
-- statement:
--   The Twist Mem construction uses the vec Mul scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemHilbertLatticeTwistIffLift.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemHilbertLatticeTwistIffLift.lean#L43-L46

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

theorem GlobalTheory.HilbFam.TwistMem.vecMul_scalar (N : ℕ) (w : Fin 2 → F) :
    Matrix.vecMul w ((((N : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ))).map (Int.cast : ℤ → F)) = (N : F) • w := by sorry
