-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_ChartIndep_chartHom_congr
-- name    : GlobalTheory.SecGlue.ChartIndep.chartHom_congr
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:50:28.467682+00:00
-- url     : https://prove2.me/theorems/2409fbef-078e-4726-af4c-118ca9eb64db
-- title:
--   Chart Indep: chart Hom congr
-- statement:
--   The Chart Indep construction uses the chart Hom congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationIndependentOfChart.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationIndependentOfChart.lean#L13-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartUniqueStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapCompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChart
import Theorems.Thm_GlobalTheory_SecGlue_CombEx_chartHom_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SecGlue
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.ChartIndep

theorem GlobalTheory.SecGlue.ChartIndep.chartHom_congr {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] {f g : Sp S ⟶ Y}
    (e : f = g) (hf : f ⁻¹ᵁ V = ⊤) (hg : g ⁻¹ᵁ V = ⊤) (x : Γ(Y, V)) :
    chartHom V f hf x = chartHom V g hg x := by sorry
