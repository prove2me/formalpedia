-- Prove2me | Theorems.Thm_GlobalTheory_EigFlat_eig_iff
-- name    : GlobalTheory.EigFlat.eig_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:06:44.10124+00:00
-- url     : https://prove2.me/theorems/dfc6fe24-aa80-42ad-87f3-6b242c36c83b
-- title:
--   Eig Flat: eig iff
-- statement:
--   The Eig Flat construction uses the eig iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CommonEigenvectorsFlatBaseChange.lean#L93-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/CommonEigenvectorsFlatBaseChange.lean#L93-L101

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_CommonEigenvectorsFlatBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix TensorProduct
open GlobalTheory
open GlobalTheory.EigFlat
variable {A : Type} [CommRing A]

theorem GlobalTheory.EigFlat.eig_iff {g : ℕ} (M : Matrix (Fin g) (Fin g) A) (ρ : A) (B : Type) [CommRing B]
    [Algebra A B] (w : Fin g → B) :
    w ᵥ* (M - ρ • (1 : Matrix (Fin g) (Fin g) A)).map (algebraMap A B) = 0 ↔
      w ᵥ* M.map (algebraMap A B) = algebraMap A B ρ • w := by sorry
