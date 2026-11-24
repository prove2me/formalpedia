-- Prove2me | Theorems.Thm_GlobalTheory_Square_Sq_Tuple_tuple_constants_ne_zero
-- name    : GlobalTheory.Square.Sq.Tuple.tuple_constants_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:25:21.060866+00:00
-- url     : https://prove2.me/theorems/fa0bd7cb-bde7-4d7a-a93e-3ff9d75e2fdc
-- title:
--   Tuple: tuple constants ne zero
-- statement:
--   The Tuple construction uses the tuple constants ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L194-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L194-L219

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

theorem GlobalTheory.Square.Sq.Tuple.tuple_constants_ne_zero {S : Sq K} {hd y : ℕ} {σ₀ : K →+* ℂ} {a : An (S.p + S.q)} {Z : Co K S.κ} {w : Pl K}
    {dl : ℝ} (h : S.Tuple σ₀ a Z w dl) (hS : S.OK hd y) : a.c0 ≠ 0 ∧ a.c ≠ 0 := by sorry
