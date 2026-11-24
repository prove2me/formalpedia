-- Prove2me | Theorems.Thm_GlobalTheory_Square_IsAwayUnit_ne_zero_and_vw
-- name    : GlobalTheory.Square.IsAwayUnit.ne_zero_and_vw
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:10:03.159544+00:00
-- url     : https://prove2.me/theorems/e6840963-60fa-4300-8487-c71aaa167e38
-- title:
--   Is Away Unit: ne zero and vw
-- statement:
--   The Is Away Unit construction uses the ne zero and vw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L166-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/TupleConstantsNeZero.lean#L166-L184

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

theorem GlobalTheory.Square.IsAwayUnit.ne_zero_and_vw {m : ℕ} {x : K} (h : IsAwayUnit m x) (w : Pl K) (hm : (m : 𝓞 K) ∉ w.asIdeal) :
    x ≠ 0 ∧ vw w x = 0 := by sorry
