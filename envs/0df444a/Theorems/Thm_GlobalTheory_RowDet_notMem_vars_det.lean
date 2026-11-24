-- Prove2me | Theorems.Thm_GlobalTheory_RowDet_notMem_vars_det
-- name    : GlobalTheory.RowDet.notMem_vars_det
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:30:27.92006+00:00
-- url     : https://prove2.me/theorems/cee78880-251d-4dfe-93a9-49aacdf4cbde
-- title:
--   Row Det: not Mem vars det
-- statement:
--   The Row Det construction uses the not Mem vars det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IrreducibleDetOfIsRelPrime.lean#L13-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IrreducibleDetOfIsRelPrime.lean#L13-L24

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

theorem GlobalTheory.RowDet.notMem_vars_det {R σ : Type*} [CommRing R] {m : Type*} [Fintype m] [DecidableEq m]
    (a : σ) (M : Matrix m m (MvPolynomial σ R)) (h : ∀ i j, a ∉ (M i j).vars) :
    a ∉ M.det.vars := by sorry
