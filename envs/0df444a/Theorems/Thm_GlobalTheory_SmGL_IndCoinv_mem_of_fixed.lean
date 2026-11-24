-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IndCoinv_mem_of_fixed
-- name    : GlobalTheory.SmGL.IndCoinv.mem_of_fixed
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T21:35:50.380127+00:00
-- url     : https://prove2.me/theorems/205b3746-5042-4c37-8bb6-94fc3746db03
-- title:
--   Ind Coinv: mem of fixed
-- statement:
--   The Ind Coinv construction uses the mem of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmIndCoinvariants.lean#L41-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmIndCoinvariants.lean#L41-L63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmIndCoinvariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.IndDual
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.IndCoinv
variable {G X U : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module ℂ X]
  [AddCommGroup U] [Module ℂ U] {P : Subgroup G} {σ : Representation ℂ P X} {ρ : Representation ℂ P U}

theorem GlobalTheory.SmGL.IndCoinv.mem_of_fixed [T2Space G] {σ : Representation ℂ G X} (hσ : IsSmooth σ) {H : Subgroup G}
    (hH : IsCompact (H : Set G)) {Γ : Type} (T : Γ → σ.IntertwiningMap σ) (M : Submodule ℂ (fixed σ H))
    (hM : ∀ γ (z : fixed σ H), (⟨T γ z, map_mem_fixed (T γ) z.2⟩ : fixed σ H) - z ∈ M) (w : fixed σ H)
    (hw : w.1 ∈ Submodule.span ℂ {y : X | ∃ γ z, y = T γ z - z}) : w ∈ M := by sorry
