-- Prove2me | Theorems.Thm_GlobalTheory_FlagSecProbe_weight_eq_zero_of_one_isSec
-- name    : GlobalTheory.FlagSecProbe.weight_eq_zero_of_one_isSec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:23.786794+00:00
-- url     : https://prove2.me/theorems/771efa0f-8741-4229-9284-f069d5f735ee
-- title:
--   Flag Sec Probe: weight eq zero of one is Sec
-- statement:
--   The Flag Sec Probe construction uses the weight eq zero of one is Sec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/WeightEqZeroOfOneIsSec.lean#L61-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/WeightEqZeroOfOneIsSec.lean#L61-L86

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UpperHalfSurvey_WeightEqZeroOfOneIsSec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD NumberField
open GlobalTheory GlobalTheory.FlagSecProbe
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem GlobalTheory.FlagSecProbe.weight_eq_zero_of_one_isSec (X : Data E r) (la : Wt X.Ψ r)
    (h : X.IsSec la (fun _ => 1)) : la = 0 := by sorry
