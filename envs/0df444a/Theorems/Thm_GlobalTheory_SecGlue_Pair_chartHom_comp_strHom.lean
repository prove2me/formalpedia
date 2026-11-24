-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Pair_chartHom_comp_strHom
-- name    : GlobalTheory.SecGlue.Pair.chartHom_comp_strHom
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:53:39.395203+00:00
-- url     : https://prove2.me/theorems/f8d3eb47-eae7-489f-938f-ce4a193c23ba
-- title:
--   Pair: chart Hom comp str Hom
-- statement:
--   The Pair construction uses the chart Hom comp str Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSquareZeroLiftBasicOpenPairAgree.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSquareZeroLiftBasicOpenPairAgree.lean#L53-L58

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

theorem GlobalTheory.SecGlue.Pair.chartHom_comp_strHom {R : Type} [CommRing R] (X : Over (Sp R)) {V : X.left.Opens}
    (hV : IsAffineOpen V) {S : Type} [CommRing S] (f : R →+* S) (u : Sp S ⟶ X.left) (hu : u ⁻¹ᵁ V = ⊤)
    (hf : u ≫ X.hom = spMap f) : (chartHom V u hu).comp (strHom X V) = f := by sorry
