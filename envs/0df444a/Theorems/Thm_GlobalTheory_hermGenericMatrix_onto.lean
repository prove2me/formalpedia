-- Prove2me | Theorems.Thm_GlobalTheory_hermGenericMatrix_onto
-- name    : GlobalTheory.hermGenericMatrix_onto
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:54:48.068775+00:00
-- url     : https://prove2.me/theorems/dbb6cc26-f8c4-4465-ae92-1f7b6d12a2f8
-- title:
--   Global Theory: herm Generic Matrix onto
-- statement:
--   The Global Theory construction uses the herm Generic Matrix onto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsHermitianDetNeZeroTwo.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsHermitianDetNeZeroTwo.lean#L18-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsHermitianDetNeZeroTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial Matrix

theorem GlobalTheory.hermGenericMatrix_onto {κ : Type} [Field κ] [CharZero κ] (n : ℕ) (e : κ) (he : e ≠ 0)
    (y : Matrix (Fin n) (Fin n) κ) :
    ∃ u : Fin n × Fin n → κ, (hermGenericMatrix n e).map (MvPolynomial.eval u) = y := by sorry
