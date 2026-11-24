-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Cocycle_eq_of_cocycle
-- name    : GlobalTheory.SecGlue.Cocycle.eq_of_cocycle
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T19:49:44.773286+00:00
-- url     : https://prove2.me/theorems/2dd872ca-c194-4d3b-9c26-50a030c56bab
-- title:
--   Cocycle: eq of cocycle
-- statement:
--   The Cocycle construction uses the eq of cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftsAgreeOfCocycle.lean#L70-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftsAgreeOfCocycle.lean#L70-L90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecHomExtOfLocalizationAwaySpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftsAgreeOfCocycle
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
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Cocycle

theorem GlobalTheory.SecGlue.Cocycle.eq_of_cocycle {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) {S : Type} [CommRing S]
    {κ : Type} [Fintype κ] (u u' c c' : Sp S ⟶ Y) (w w' : κ → (Sp S ⟶ Y)) (a b : κ → S)
    (hab : ∑ k, a k * b k = 1) (h : IsCombIn W u c w a) (h' : IsCombIn W u' c' w' a)
    (hco : ∀ k, IsCombIn W u' (w k) ![w' k, u] ![1, 1 - b k]) : c = c' := by sorry
