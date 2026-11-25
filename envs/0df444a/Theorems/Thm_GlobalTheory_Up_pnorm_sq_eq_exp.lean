-- Prove2me | Theorems.Thm_GlobalTheory_Up_pnorm_sq_eq_exp
-- name    : GlobalTheory.Up.pnorm_sq_eq_exp
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T15:27:26.215813+00:00
-- url     : https://prove2.me/theorems/e73c52ee-afbd-409a-a29e-a8fb0d7ed5a3
-- title:
--   Up: pnorm sq eq exp
-- statement:
--   The Up construction uses the pnorm sq eq exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/UpperBounds/SumNormSqWPos.lean#L107-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/UpperBounds/SumNormSqWPos.lean#L107-L118

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_UpperBounds_SumNormSqWPos
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

theorem GlobalTheory.Up.pnorm_sq_eq_exp (hx : x ∈ X.dom) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) :
    X.pnorm la P x ^ 2 = Real.exp (-phla X la x) * ‖P x‖ ^ 2 := by sorry
