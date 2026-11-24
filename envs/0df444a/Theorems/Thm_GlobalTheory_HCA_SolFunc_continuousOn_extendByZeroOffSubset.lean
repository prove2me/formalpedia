-- Prove2me | Theorems.Thm_GlobalTheory_HCA_SolFunc_continuousOn_extendByZeroOffSubset
-- name    : GlobalTheory.HCA.SolFunc.continuousOn_extendByZeroOffSubset
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T14:00:39.873083+00:00
-- url     : https://prove2.me/theorems/f29cc401-225a-456f-9180-4c0f53d0fc6d
-- title:
--   Sol Func: continuous On extend By Zero Off Subset
-- statement:
--   The Sol Func construction uses the continuous On extend By Zero Off Subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EllipticSystemDerivativeContinuousFunctional.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EllipticSystemDerivativeContinuousFunctional.lean#L31-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AestronglyMeasurableExtendByZeroOffSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsContinuousFunctionalIterPartialDerivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EllipticSystemDerivativeContinuousFunctional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory
open scoped ContDiff BoundedContinuousFunction
noncomputable section
open GlobalTheory GlobalTheory.HCA GlobalTheory.HCA.SolFunc
variable {d : ℕ}

theorem GlobalTheory.HCA.SolFunc.continuousOn_extendByZeroOffSubset {U : Set (E d)} (u : U →ᵇ ℂ) : ContinuousOn (ext0 U u) U := by sorry
