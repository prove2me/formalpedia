-- Prove2me | Theorems.Thm_GlobalTheory_exists_cols_det_ne_zero_of_mul
-- name    : GlobalTheory.exists_cols_det_ne_zero_of_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:36:05.551795+00:00
-- url     : https://prove2.me/theorems/e2003bce-a7fb-48fe-8c06-101e1823d49c
-- title:
--   Global Theory: exists cols det ne zero of mul
-- statement:
--   The Global Theory construction uses the exists cols det ne zero of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsColsDetNeZeroOfMul.lean#L51-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsColsDetNeZeroOfMul.lean#L51-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsColsDetNeZeroOfMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix

theorem GlobalTheory.exists_cols_det_ne_zero_of_mul {Ω : Type} [Field Ω] {n r : ℕ}
    (R : Matrix (Fin r) (Fin n) Ω) (u : Matrix (Fin n) (Fin r) Ω) (hd : (R * u).det ≠ 0) :
    ∃ κ : Fin r → Fin n, (R.submatrix id κ).det ≠ 0 := by sorry
