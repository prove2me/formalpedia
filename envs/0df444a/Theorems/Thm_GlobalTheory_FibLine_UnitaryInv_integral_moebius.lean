-- Prove2me | Theorems.Thm_GlobalTheory_FibLine_UnitaryInv_integral_moebius
-- name    : GlobalTheory.FibLine.UnitaryInv.integral_moebius
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:23:23.422796+00:00
-- url     : https://prove2.me/theorems/3637cc0f-06a3-42e5-a63b-58dc5646c819
-- title:
--   Unitary Inv: integral moebius
-- statement:
--   The Unitary Inv construction uses the integral moebius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DivFractionsBilinearFormula.lean#L26-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DivFractionsBilinearFormula.lean#L26-L82

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

theorem GlobalTheory.FibLine.UnitaryInv.integral_moebius (a b c d : ℂ) (hD : a * d - b * c ≠ 0) (G : ℂ → ℂ) :
    ∫ y : ℂ, G y = ∫ x : ℂ, (Complex.normSq ((a * d - b * c) / (a + b * x) ^ 2)) •
      G ((c + d * x) / (a + b * x)) := by sorry
