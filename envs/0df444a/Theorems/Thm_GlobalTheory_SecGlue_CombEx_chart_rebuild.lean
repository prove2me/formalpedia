-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_CombEx_chart_rebuild
-- name    : GlobalTheory.SecGlue.CombEx.chart_rebuild
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:20:23.297607+00:00
-- url     : https://prove2.me/theorems/646fb01f-9e09-4cbb-b15d-10910da98cc0
-- title:
--   Comb Ex: chart rebuild
-- statement:
--   The Comb Ex construction uses the chart rebuild property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineCombinationSquareZeroLiftsChart.lean#L9-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineCombinationSquareZeroLiftsChart.lean#L9-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.CombEx

theorem GlobalTheory.SecGlue.CombEx.chart_rebuild {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (x : Sp S ⟶ Y) (hx : x ⁻¹ᵁ V = ⊤) : spMap (chartHom V x hx) ≫ hV.fromSpec = x := by sorry
