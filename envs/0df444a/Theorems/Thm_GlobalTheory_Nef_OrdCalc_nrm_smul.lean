-- Prove2me | Theorems.Thm_GlobalTheory_Nef_OrdCalc_nrm_smul
-- name    : GlobalTheory.Nef.OrdCalc.nrm_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:01:57.231979+00:00
-- url     : https://prove2.me/theorems/35ffc267-3ecb-4705-8833-f8dc78a88d92
-- title:
--   Ord Calc: nrm smul
-- statement:
--   The Ord Calc construction uses the nrm smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceOrderCalculus.lean#L62-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FunctionFieldPlaceOrderCalculus.lean#L62-L74

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

theorem GlobalTheory.Nef.OrdCalc.nrm_smul (v : Place k F) (n : ℕ) (x : Fin n → F) (c : F) :
    nrm v (c • x) = v.1 c * nrm v x := by sorry
