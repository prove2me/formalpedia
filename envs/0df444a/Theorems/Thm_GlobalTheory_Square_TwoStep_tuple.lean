-- Prove2me | Theorems.Thm_GlobalTheory_Square_TwoStep_tuple
-- name    : GlobalTheory.Square.TwoStep.tuple
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:25:29.08281+00:00
-- url     : https://prove2.me/theorems/04d50d02-5e2f-4191-a6f1-4f5fc167d1db
-- title:
--   Two Step: tuple
-- statement:
--   The Two Step construction uses the tuple property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L268-L293
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L268-L293

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

theorem GlobalTheory.Square.TwoStep.tuple (σ₀ : K →+* ℂ) (w : Pl K) {n m Q : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) (hQ : Q ≠ 0) :
    (square K).Tuple σ₀ (numbers n m Q) (coords K (m * Q)) w (vw w ((2 : ℕ) : K) : ℝ) := by sorry
