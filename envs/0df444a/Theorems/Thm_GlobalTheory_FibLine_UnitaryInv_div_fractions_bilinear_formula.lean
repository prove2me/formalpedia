-- Prove2me | Theorems.Thm_GlobalTheory_FibLine_UnitaryInv_div_fractions_bilinear_formula
-- name    : GlobalTheory.FibLine.UnitaryInv.div_fractions_bilinear_formula
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:23:28.918814+00:00
-- url     : https://prove2.me/theorems/52bc5b68-9f17-4903-9fa1-8467a2b48441
-- title:
--   Unitary Inv: div fractions bilinear formula
-- statement:
--   The Unitary Inv construction uses the div fractions bilinear formula property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DivFractionsBilinearFormula.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DivFractionsBilinearFormula.lean#L102-L105

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

theorem GlobalTheory.FibLine.UnitaryInv.div_fractions_bilinear_formula (h0 h1 h2 h3 A B C D N : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hN : N ≠ 0) :
    (h0 + h1 * (C / A) + h2 * (D / B) + h3 * (C / A * (D / B))) / (N / (A * B))
      = (h0 * (A * B) + h1 * (C * B) + h2 * (D * A) + h3 * (C * D)) / N := by sorry
