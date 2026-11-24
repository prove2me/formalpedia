-- Prove2me | Theorems.Thm_GlobalTheory_RowDet_det_mem_subalgebra
-- name    : GlobalTheory.RowDet.det_mem_subalgebra
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:30:42.739136+00:00
-- url     : https://prove2.me/theorems/719545b4-9157-41b7-b007-1fe090fc4422
-- title:
--   Row Det: det mem subalgebra
-- statement:
--   The Row Det construction uses the det mem subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IrreducibleDetOfIsRelPrime.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IrreducibleDetOfIsRelPrime.lean#L7-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.RowDet

theorem GlobalTheory.RowDet.det_mem_subalgebra {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {m : Type*} [Fintype m] [DecidableEq m] (S : Subalgebra R A) (M : Matrix m m A)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by sorry
