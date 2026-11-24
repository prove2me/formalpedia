-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Pair_chartHom_congr
-- name    : GlobalTheory.SecGlue.Pair.chartHom_congr
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:52:56.538417+00:00
-- url     : https://prove2.me/theorems/c14891df-8d69-4384-bfe8-a31d192604cc
-- title:
--   Pair: chart Hom congr
-- statement:
--   The Pair construction uses the chart Hom congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSquareZeroLiftBasicOpenPairAgree.lean#L39-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSquareZeroLiftBasicOpenPairAgree.lean#L39-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSqZeroExtendLocalizationAwayPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSquareZeroLiftBasicOpenPairAgree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Pair

theorem GlobalTheory.SecGlue.Pair.chartHom_congr {Y : Scheme.{0}} (V : Y.Opens) {S : Type} [CommRing S] {x x' : Sp S ⟶ Y}
    (e : x = x') (h : x ⁻¹ᵁ V = ⊤) (h' : x' ⁻¹ᵁ V = ⊤) : chartHom V x h = chartHom V x' h' := by sorry
