-- Prove2me | Theorems.Thm_GlobalTheory_Nef_OrdCalc_unimod_mul_inv
-- name    : GlobalTheory.Nef.OrdCalc.unimod_mul_inv
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:59:14.67245+00:00
-- url     : https://prove2.me/theorems/701a84fc-904b-442b-a8e9-f2d634deaa09
-- title:
--   Ord Calc: unimod mul inv
-- statement:
--   The Ord Calc construction uses the unimod mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceOrderCalculus.lean#L115-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceOrderCalculus.lean#L115-L122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FunctionFieldPlaceOrderCalculus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef
set_option autoImplicit false
open GlobalTheory GlobalTheory.Nef GlobalTheory.Nef.OrdCalc
variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem GlobalTheory.Nef.OrdCalc.unimod_mul_inv (v : Place k F) (n : ℕ) (u u' : Matrix (Fin n) (Fin n) F)
    (hu : Unimod v u) (hu' : Unimod v u') : Unimod v (u * u') ∧ Unimod v u⁻¹ := by sorry
