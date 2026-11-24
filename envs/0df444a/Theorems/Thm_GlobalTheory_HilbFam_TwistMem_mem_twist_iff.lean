-- Prove2me | Theorems.Thm_GlobalTheory_HilbFam_TwistMem_mem_twist_iff
-- name    : GlobalTheory.HilbFam.TwistMem.mem_twist_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:20:53.59333+00:00
-- url     : https://prove2.me/theorems/0feb54bd-0b6b-491e-b06a-0de6837595d8
-- title:
--   Twist Mem: mem twist iff
-- statement:
--   The Twist Mem construction uses the mem twist iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemHilbertLatticeTwistIffLift.lean#L48-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MemHilbertLatticeTwistIffLift.lean#L48-L65

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

theorem GlobalTheory.HilbFam.TwistMem.mem_twist_iff (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F)
    (A : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → F) (hL : L ≤ stdLat F) :
    (v ∈ twist N L (A.map (Int.cast : ℤ → ZMod N)) ↔
      ∃ y ∈ L, ∃ w ∈ stdLat F, v = Matrix.vecMul y (A.map (Int.cast : ℤ → F)) + (N : F) • w) := by sorry
