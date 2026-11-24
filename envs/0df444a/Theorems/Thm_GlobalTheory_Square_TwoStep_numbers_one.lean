-- Prove2me | Theorems.Thm_GlobalTheory_Square_TwoStep_numbers_one
-- name    : GlobalTheory.Square.TwoStep.numbers_one
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:25:19.771035+00:00
-- url     : https://prove2.me/theorems/55b74e6a-b92b-4d95-90af-8a8e3feca6c9
-- title:
--   Two Step: numbers one
-- statement:
--   The Two Step construction uses the numbers one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L297-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L297-L298

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementH
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_TupleConstantsNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)
noncomputable section
open GlobalTheory GlobalTheory.Square
variable {K : Type} [Field K] [NumberField K] [StarRing K]
attribute [instance] Co.finX
attribute [instance] Sq.finκ
open GlobalTheory.Square.TwoStep
omit [NumberField K] [StarRing K]

theorem GlobalTheory.Square.TwoStep.numbers_one : numbers 1 1 1 = (square K).base := by sorry
