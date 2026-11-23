-- Prove2me | Theorems.Thm_GenFrameSpan_det_submatrix_fun
-- name    : GenFrameSpan.det_submatrix_fun
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:08:07.956736+00:00
-- url     : https://prove2.me/theorems/08faafe4-3144-49ca-bcb5-c5d5a87a56de
-- title:
--   Gen Frame Span: det submatrix fun
-- statement:
--   The Gen Frame Span construction uses the det submatrix fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/DetSubmatrixFun.lean#L19-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/DetSubmatrixFun.lean#L19-L50

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MonomialFrameSpan_DetSubmatrixFun
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open GenFrameSpan

theorem GenFrameSpan.det_submatrix_fun {R : Type*} [CommRing R] {p n : ℕ} (M : Matrix (Fin p) (Fin n) R)
    (f : Fin p → Fin n) :
    (M.submatrix id f).det = 0 ∨ ∃ (J : Fin p ↪o Fin n) (e : ℤ),
      (M.submatrix id f).det = (e : R) * (M.submatrix id J).det := by sorry
