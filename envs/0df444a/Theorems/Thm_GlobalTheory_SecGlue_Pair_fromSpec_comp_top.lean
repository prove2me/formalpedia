-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Pair_fromSpec_comp_top
-- name    : GlobalTheory.SecGlue.Pair.fromSpec_comp_top
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:50:07.951586+00:00
-- url     : https://prove2.me/theorems/2caab3ff-ba94-42e1-a511-caa8f15ca51d
-- title:
--   Pair: from Spec comp top
-- statement:
--   The Pair construction uses the from Spec comp top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSquareZeroLiftBasicOpenPairAgree.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSquareZeroLiftBasicOpenPairAgree.lean#L28-L30

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

theorem GlobalTheory.SecGlue.Pair.fromSpec_comp_top {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) {S : Type} [CommRing S]
    (χ : Γ(Y, V) →+* S) : (spMap χ ≫ hV.fromSpec) ⁻¹ᵁ V = ⊤ := by sorry
