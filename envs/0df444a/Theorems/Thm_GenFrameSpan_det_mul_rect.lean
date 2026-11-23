-- Prove2me | Theorems.Thm_GenFrameSpan_det_mul_rect
-- name    : GenFrameSpan.det_mul_rect
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:43:18.447944+00:00
-- url     : https://prove2.me/theorems/c3184cf3-1b96-4a1f-8516-41051be47a90
-- title:
--   Gen Frame Span: det mul rect
-- statement:
--   The Gen Frame Span construction uses the det mul rect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/DetSubmatrixFun.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MonomialFrameSpan/DetSubmatrixFun.lean#L9-L17

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

theorem GenFrameSpan.det_mul_rect {R : Type*} [CommRing R] {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det = ∑ f : Fin k → Fin n, (∏ i, B (f i) i) * (A.submatrix id f).det := by sorry
