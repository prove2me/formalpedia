-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_IndCoinv_mem_of_bump
-- name    : GlobalTheory.SmGL.IndCoinv.mem_of_bump
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:36:05.548653+00:00
-- url     : https://prove2.me/theorems/46480bbc-37f4-4e78-af6b-fd309fe7b51b
-- title:
--   Ind Coinv: mem of bump
-- statement:
--   The Ind Coinv construction uses the mem of bump property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmIndCoinvariants.lean#L23-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmIndCoinvariants.lean#L23-L34

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

theorem GlobalTheory.SmGL.IndCoinv.mem_of_bump {K : Subgroup G} (hK : IsCompact (K : Set G))
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ x ∈ K, g = p * x)
    (hb : ∀ U ∈ nhds (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧ (J : Set G) ⊆ U ∧ J ≤ K ∧
      ∀ x ∈ K, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (Z : Submodule ℂ (smoothPart (ind P σ))) (hZ : ∀ g, ∀ f ∈ Z, smInd P σ g f ∈ Z)
    (h : ∀ (J : Subgroup G) (hJ : IsOpen (J : Set G)), J ≤ K → ∀ w, bump σ hJ w ∈ Z)
    (f : smoothPart (ind P σ)) : f ∈ Z := by sorry
