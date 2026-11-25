-- Prove2me | Theorems.Thm_GlobalTheory_Up_Wdiv_eq_exp
-- name    : GlobalTheory.Up.Wdiv_eq_exp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:26:57.102008+00:00
-- url     : https://prove2.me/theorems/0d74c43e-6fab-5117-a345-4a5b9b9e3487
-- title:
--   Up: Wdiv eq exp
-- statement:
--   The Up construction uses the Wdiv eq exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/UpperBounds/SumNormSqWPos.lean#L73-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/UpperBounds/SumNormSqWPos.lean#L73-L83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SumNormSqWPos
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open GlobalTheory GlobalTheory.Up
variable {r : ℕ} {X : Data E r} (Xa : ArchInM X) (Fl : FlatM X Xa) (n : ℕ) {x : Frame X.Ψ r}

theorem GlobalTheory.Up.Wdiv_eq_exp (hx : x ∈ X.dom) (hs : ∃ k, Fl.s k x ≠ 0) :
    Wdiv X Xa Fl n x = ENNReal.ofReal (Real.exp (-Psdiv X Xa Fl n x)) := by sorry
