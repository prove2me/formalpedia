-- Prove2me | Theorems.Thm_GlobalTheory_ZeroFreeComplex_half_lt_log
-- name    : GlobalTheory.ZeroFreeComplex.half_lt_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:50:13.046177+00:00
-- url     : https://prove2.me/theorems/1f4c64b6-7d9b-4889-b0f2-01a5c6c56481
-- title:
--   Zero Free Complex: half lt log
-- statement:
--   The Zero Free Complex construction uses the half lt log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionConjEqZero.lean#L139-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/LFunctionConjEqZero.lean#L139-L143

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivativeBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegSumLogDerivNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivDirichletLFunctionLocalZeroSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegReLogDerivPrincipalLFunctionLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionConjEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open scoped ComplexConjugate
open GlobalTheory GlobalTheory.ZeroFreeComplex

theorem GlobalTheory.ZeroFreeComplex.half_lt_log (q : ℕ) [NeZero q] (t : ℝ) : 1 / 2 < Real.log (q * (|t| + 2)) := by sorry
