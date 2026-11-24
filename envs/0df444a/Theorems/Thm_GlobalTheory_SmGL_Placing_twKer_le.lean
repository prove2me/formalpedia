-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_Placing_twKer_le
-- name    : GlobalTheory.SmGL.Placing.twKer_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:14:18.298226+00:00
-- url     : https://prove2.me/theorems/f1379764-5b08-4aab-9442-4792af539ba6
-- title:
--   Placing: tw Ker le
-- statement:
--   The Placing construction uses the tw Ker le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ParIndJacPlacing.lean#L59-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ParIndJacPlacing.lean#L59-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ParIndJacPlacing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.Placing
variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V]
open ValuativeRel MeasureTheory
variable {F G M V : Type} [Field F] [Group G] [Group M] [AddCommGroup V] [Module F V]

theorem GlobalTheory.SmGL.Placing.twKer_le (π : Representation F G V)
    {N N' : Subgroup G} (w : G) (h : ∀ u ∈ N, w * u * w⁻¹ ∈ N') :
    _root_.GlobalTheory.PRep.twKer π N 1 ≤ (_root_.GlobalTheory.PRep.twKer π N' 1).comap (π w) := by sorry
