-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_TwistMem_exists_lift_diff
-- name    : GlobalTheory.HilbFam.TwistMem.exists_lift_diff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:20:38.115516+00:00
-- url     : https://prove2.me/theorems/26b4de5c-e968-47ea-b5c5-bd51fe3925d6
-- title:
--   Twist Mem: exists lift diff
-- statement:
--   The Twist Mem construction uses the exists lift diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemHilbertLatticeTwistIffLift.lean#L26-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemHilbertLatticeTwistIffLift.lean#L26-L41

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

theorem GlobalTheory.HilbFam.TwistMem.exists_lift_diff (N : ℕ) (A : Matrix (Fin 2) (Fin 2) ℤ) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℤ,
      ((A.map (Int.cast : ℤ → ZMod N)).map (ZMod.cast : ZMod N → ℤ)).map (Int.cast : ℤ → F)
        = A.map (Int.cast : ℤ → F) + (N : F) • B.map (Int.cast : ℤ → F) := by sorry
