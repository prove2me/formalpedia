-- Prove2me | Theorems.Thm_GlobalTheory_FlagSecProbe_pnorm_eq_zero_iff
-- name    : GlobalTheory.FlagSecProbe.pnorm_eq_zero_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:05:16.156807+00:00
-- url     : https://prove2.me/theorems/4e1655af-9252-5754-a01f-afe4f86c13e6
-- title:
--   Flag Sec Probe: pnorm eq zero iff
-- statement:
--   The Flag Sec Probe construction uses the pnorm eq zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/WeightEqZeroOfOneIsSec.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UpperHalfSurvey/WeightEqZeroOfOneIsSec.lean#L34-L42

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

theorem GlobalTheory.FlagSecProbe.pnorm_eq_zero_iff (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) : X.pnorm la P x = 0 ↔ P x = 0 := by sorry
