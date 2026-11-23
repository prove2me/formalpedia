-- Prove2me | Theorems.Thm_GlobalTheory_RowDet_det_updateRow_single
-- name    : GlobalTheory.RowDet.det_updateRow_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:00:33.818546+00:00
-- url     : https://prove2.me/theorems/3d214e22-12c4-48a9-80e6-95f75c33a8e3
-- title:
--   Row Det: det update Row single
-- statement:
--   The Row Det construction uses the det update Row single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IrreducibleDetOfIsRelPrime.lean#L26-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IrreducibleDetOfIsRelPrime.lean#L26-L39

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

theorem GlobalTheory.RowDet.det_updateRow_single {A : Type*} [CommRing A] {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) A) :
    (M.updateRow (Fin.last n) (Pi.single (Fin.last n) 1)).det =
      (M.submatrix Fin.castSucc Fin.castSucc).det := by sorry
