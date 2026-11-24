-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_ChartIndep_locMap_ker
-- name    : GlobalTheory.SecGlue.ChartIndep.locMap_ker
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:49:48.978741+00:00
-- url     : https://prove2.me/theorems/c6437eb0-5e94-4ff3-8ff1-e790604327a6
-- title:
--   Chart Indep: loc Map ker
-- statement:
--   The Chart Indep construction uses the loc Map ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationIndependentOfChart.lean#L74-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationIndependentOfChart.lean#L74-L102

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

theorem GlobalTheory.SecGlue.ChartIndep.locMap_ker (hk : RingHom.ker q ^ 2 = ⊥) : RingHom.ker (locMap q s) ^ 2 = ⊥ := by sorry
