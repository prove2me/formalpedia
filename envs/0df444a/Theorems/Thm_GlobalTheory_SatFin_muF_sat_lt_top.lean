-- Prove2me | Theorems.Thm_GlobalTheory_SatFin_muF_sat_lt_top
-- name    : GlobalTheory.SatFin.muF_sat_lt_top
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:30:15.553052+00:00
-- url     : https://prove2.me/theorems/32cfd890-2183-5cca-a567-bbe0c3f60d33
-- title:
--   Sat Fin: mu F sat lt top
-- statement:
--   The Sat Fin construction uses the mu F sat lt top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MuFLtTopOfIsCompact.lean#L46-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/MuFLtTopOfIsCompact.lean#L46-L101

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

theorem GlobalTheory.SatFin.muF_sat_lt_top (hI : MeasInvStatement (E := E)) (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r)
    (hx0 : IsOrth X x0) (C : Set (Frame X.Ψ r)) (hK : IsCompact C) (hC : C ⊆ X.dom) :
    muF X x0 (sat X x0 C) < ⊤ := by sorry
