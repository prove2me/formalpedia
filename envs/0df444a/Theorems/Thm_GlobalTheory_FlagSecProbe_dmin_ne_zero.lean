-- Prove2me | Theorems.Thm_GlobalTheory_FlagSecProbe_dmin_ne_zero
-- name    : GlobalTheory.FlagSecProbe.dmin_ne_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T13:31:38.878314+00:00
-- url     : https://prove2.me/theorems/44f815df-af13-408a-a69a-acf1e64ad19f
-- title:
--   Flag Sec Probe: dmin ne zero
-- statement:
--   The Flag Sec Probe construction uses the dmin ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/WeightEqZeroOfOneIsSec.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/WeightEqZeroOfOneIsSec.lean#L28-L32

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

theorem GlobalTheory.FlagSecProbe.dmin_ne_zero (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ)
    (i : Fin (r + 1)) : dmin X.Gm x τ i ≠ 0 := by sorry
