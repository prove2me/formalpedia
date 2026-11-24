-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Red_comp_overR
-- name    : GlobalTheory.SecGlue.Red.comp_overR
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:48:57.115392+00:00
-- url     : https://prove2.me/theorems/3a53ab50-4ed2-40d8-9cb5-d66ad25b0898
-- title:
--   Red: comp over R
-- statement:
--   The Red construction uses the comp over R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowCocycle.lean#L70-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPowCocycle.lean#L70-L74

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapEqOfRed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapCompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AlgHomEqMulPowOfEqLocalizationAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowCocycle
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
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Red

theorem GlobalTheory.SecGlue.Red.comp_overR {R : Type} [CommRing R] (X : Over (Sp R)) (a : R) {S : Type} [CommRing S] [Algebra R S]
    (ρ : Localization.Away a →+* S) (hρ : ρ.comp (algebraMap R _) = algebraMap R S)
    (u : Sp (Localization.Away a) ⟶ X.left) (hu : u ≫ X.hom = spMap (algebraMap R _)) :
    (spMap ρ ≫ u) ≫ X.hom = spMap (algebraMap R S) := by sorry
