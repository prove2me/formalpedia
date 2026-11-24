-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_ChartIndep_eq_zero_of_loc
-- name    : GlobalTheory.SecGlue.ChartIndep.eq_zero_of_loc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:49:49.983714+00:00
-- url     : https://prove2.me/theorems/cb9ce2cd-455d-4dae-a097-9e16000acb42
-- title:
--   Chart Indep: eq zero of loc
-- statement:
--   The Chart Indep construction uses the eq zero of loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationIndependentOfChart.lean#L120-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationIndependentOfChart.lean#L120-L134

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

theorem GlobalTheory.SecGlue.ChartIndep.eq_zero_of_loc {S : Type} [CommRing S] (D : S)
    (h : ∀ p : Ideal S, p.IsMaximal → ∃ s ∉ p, algebraMap S (Localization.Away s) D = 0) : D = 0 := by sorry
