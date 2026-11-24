-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_ChartIndep_chartHom_mono
-- name    : GlobalTheory.SecGlue.ChartIndep.chartHom_mono
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:49:56.979395+00:00
-- url     : https://prove2.me/theorems/db412b90-f90e-4e4d-9837-7a5f95c73ab1
-- title:
--   Chart Indep: chart Hom mono
-- statement:
--   The Chart Indep construction uses the chart Hom mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationIndependentOfChart.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationIndependentOfChart.lean#L33-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartUniqueStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapCompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChart
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

theorem GlobalTheory.SecGlue.ChartIndep.chartHom_mono {Y : Scheme.{0}} {W V : Y.Opens} (hWV : W ≤ V) {S : Type} [CommRing S]
    (f : Sp S ⟶ Y) (hW : f ⁻¹ᵁ W = ⊤) (hV : f ⁻¹ᵁ V = ⊤) (x : Γ(Y, V)) :
    chartHom V f hV x = chartHom W f hW (Y.presheaf.map (homOfLE hWV).op x) := by sorry
