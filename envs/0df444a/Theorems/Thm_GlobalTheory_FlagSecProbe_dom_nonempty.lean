-- Prove2me | Theorems.Thm_GlobalTheory_FlagSecProbe_dom_nonempty
-- name    : GlobalTheory.FlagSecProbe.dom_nonempty
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T13:31:59.745152+00:00
-- url     : https://prove2.me/theorems/283ee4ac-532c-4e43-9309-eec7f360f554
-- title:
--   Flag Sec Probe: dom nonempty
-- statement:
--   The Flag Sec Probe construction uses the dom nonempty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/WeightEqZeroOfOneIsSec.lean#L10-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/WeightEqZeroOfOneIsSec.lean#L10-L26

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

theorem GlobalTheory.FlagSecProbe.dom_nonempty (X : Data E r) : X.dom.Nonempty := by sorry
