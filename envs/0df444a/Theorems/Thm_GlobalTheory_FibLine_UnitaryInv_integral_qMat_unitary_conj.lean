-- Prove2me | Theorems.Thm_GlobalTheory_FibLine_UnitaryInv_integral_qMat_unitary_conj
-- name    : GlobalTheory.FibLine.UnitaryInv.integral_qMat_unitary_conj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:23:36.596963+00:00
-- url     : https://prove2.me/theorems/5b031ba5-6a7c-43d5-913c-7614a67e7c8f
-- title:
--   Unitary Inv: integral q Mat unitary conj
-- statement:
--   The Unitary Inv construction uses the integral q Mat unitary conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DivFractionsBilinearFormula.lean#L107-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DivFractionsBilinearFormula.lean#L107-L164

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HPolyAddTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DivFractionsBilinearFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MeasureTheory MvPolynomial GlobalTheory.FibLine
open GlobalTheory GlobalTheory.FibLine GlobalTheory.FibLine.UnitaryInv

theorem GlobalTheory.FibLine.UnitaryInv.integral_qMat_unitary_conj (U : Matrix (Fin 2) (Fin 2) ℂ) (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (H : Matrix (Fin 2) (Fin 2) ℂ) (k : ℕ) :
    ∫ x : ℂ, qMat (U * H * star U) x ^ k * (fsDens x : ℂ) = ∫ x : ℂ, qMat H x ^ k * (fsDens x : ℂ) := by sorry
