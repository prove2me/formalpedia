-- Prove2me | Theorems.Thm_GlobalTheory_LLocal_analyticOrderNatAt_comp_const_add
-- name    : GlobalTheory.LLocal.analyticOrderNatAt_comp_const_add
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:55:46.005976+00:00
-- url     : https://prove2.me/theorems/d13ad5db-5350-4cf0-8c81-125f2a6e4a62
-- title:
--   LLocal: analytic Order Nat At comp const add
-- statement:
--   The LLocal construction uses the analytic Order Nat At comp const add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivDirichletLFunctionLocalZeroSum.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LogDerivDirichletLFunctionLocalZeroSum.lean#L9-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtMellinSummatory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormOneSubConjMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivDirichletLFunctionLocalZeroSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.LLocal

theorem GlobalTheory.LLocal.analyticOrderNatAt_comp_const_add (g : ℂ → ℂ) (c w : ℂ) :
    analyticOrderNatAt (fun z => g (c + z)) w = analyticOrderNatAt g (c + w) := by sorry
