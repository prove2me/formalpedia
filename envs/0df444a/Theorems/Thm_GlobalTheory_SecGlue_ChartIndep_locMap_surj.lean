-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_ChartIndep_locMap_surj
-- name    : GlobalTheory.SecGlue.ChartIndep.locMap_surj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:49:55.052213+00:00
-- url     : https://prove2.me/theorems/d1e0a2da-a300-4759-8a92-7ceb6aa775fe
-- title:
--   Chart Indep: loc Map surj
-- statement:
--   The Chart Indep construction uses the loc Map surj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationIndependentOfChart.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationIndependentOfChart.lean#L70-L72

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
variable {S T : Type} [CommRing S] [CommRing T] (q : S →+* T) (s : S)

theorem GlobalTheory.SecGlue.ChartIndep.locMap_surj (hq : Function.Surjective q) : Function.Surjective (locMap q s) := by sorry
