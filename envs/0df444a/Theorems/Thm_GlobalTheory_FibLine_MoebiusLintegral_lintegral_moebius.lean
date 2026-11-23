-- Prove2me | Theorems.Thm_GlobalTheory_FibLine_MoebiusLintegral_lintegral_moebius
-- name    : GlobalTheory.FibLine.MoebiusLintegral.lintegral_moebius
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:12.69979+00:00
-- url     : https://prove2.me/theorems/8670f4d7-e0f1-42e8-8ee3-2c58174678ce
-- title:
--   Moebius Lintegral: lintegral moebius
-- statement:
--   The Moebius Lintegral construction uses the lintegral moebius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MobiusChangeOfVariables.lean#L13-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MobiusChangeOfVariables.lean#L13-L56

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DivFractionsBilinearFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MobiusChangeOfVariables
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open GlobalTheory GlobalTheory.FibLine GlobalTheory.FibLine.MoebiusLintegral
open GlobalTheory.FibLine.UnitaryInv

theorem GlobalTheory.FibLine.MoebiusLintegral.lintegral_moebius (β c : ℂ) (hc : c ≠ 0) (H : ℂ → ℝ≥0∞) (_hH : Measurable H) :
    ∫⁻ x : ℂ, ENNReal.ofReal (‖c / (1 + β * x) ^ 2‖ ^ 2) * H (c * x / (1 + β * x)) = ∫⁻ y : ℂ, H y := by sorry
