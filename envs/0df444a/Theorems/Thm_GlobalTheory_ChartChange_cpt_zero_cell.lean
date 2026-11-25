-- Prove2me | Theorems.Thm_GlobalTheory_ChartChange_cpt_zero_cell
-- name    : GlobalTheory.ChartChange.cpt_zero_cell
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:31:50.250447+00:00
-- url     : https://prove2.me/theorems/4e21230c-2ee3-4c85-a9d6-7680bba66342
-- title:
--   Chart Change: cpt zero cell
-- statement:
--   The Chart Change construction uses the cpt zero cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LintegralBallLtTopOfLocalInverse.lean#L90-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/LintegralBallLtTopOfLocalInverse.lean#L90-L96

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_ExtFStatementPfA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_LintegralBallLtTopOfLocalInverse
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
open GlobalTheory GlobalTheory.ChartChange
open Filter
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ExtFPf

theorem GlobalTheory.ChartChange.cpt_zero_cell {r : ℕ} {X : Data E r} {x1 b : Frame X.Ψ r} (D : LUData X x1) (ho : IsOrth X x1)
    (hb : b ∈ Bor X.Ψ r) :
    cpt X (rmul x1 b) 0 ∈ cell D ∧ D.zOf (cpt X (rmul x1 b) 0) = 0 := by sorry
