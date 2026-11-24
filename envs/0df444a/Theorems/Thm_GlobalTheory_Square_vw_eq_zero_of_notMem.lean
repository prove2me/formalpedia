-- Prove2me | Theorems.Thm_GlobalTheory_Square_vw_eq_zero_of_notMem
-- name    : GlobalTheory.Square.vw_eq_zero_of_notMem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:24:50.186561+00:00
-- url     : https://prove2.me/theorems/09de1a00-a282-4ca7-9423-8b891d1d9156
-- title:
--   Square: vw eq zero of not Mem
-- statement:
--   The Square construction uses the vw eq zero of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L152-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L152-L164

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
omit [StarRing K]

theorem GlobalTheory.Square.vw_eq_zero_of_notMem (w : Pl K) {a : 𝓞 K} (ha : a ∉ w.asIdeal) : vw w (a : K) = 0 := by sorry
