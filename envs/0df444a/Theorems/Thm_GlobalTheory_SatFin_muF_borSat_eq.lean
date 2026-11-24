-- Prove2me | Theorems.Thm_GlobalTheory_SatFin_muF_borSat_eq
-- name    : GlobalTheory.SatFin.muF_borSat_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:46:39.954931+00:00
-- url     : https://prove2.me/theorems/be5f6d2e-4b5a-47f3-a8c6-08ceb59fea5b
-- title:
--   Sat Fin: mu F bor Sat eq
-- statement:
--   The Sat Fin construction uses the mu F bor Sat eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MuFLtTopOfIsCompact.lean#L30-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MuFLtTopOfIsCompact.lean#L30-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_LUStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MeasurableSetBorSat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MuFLtTopOfIsCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.SatFin
open GlobalTheory.FrameMeas
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.SatFin.muF_borSat_eq (hI : MeasInvStatement (E := E)) {r : ℕ} (X : Data E r)
    {x0 x1 : Frame X.Ψ r} (h0 : IsOrth X x0) (h1 : IsOrth X x1) {C : Set (Frame X.Ψ r)}
    (hK : IsCompact C) (hC : C ⊆ X.dom) :
    muF X x0 (cpt X x0 ⁻¹' borSat X C) = muF X x1 (cpt X x1 ⁻¹' borSat X C) := by sorry
