-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_trace_coind_mul_card
-- name    : GlobalTheory.BadShare.trace_coind_mul_card
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T23:59:20.560858+00:00
-- url     : https://prove2.me/theorems/60e1189c-4a53-419a-b5e4-8630870cdaa3
-- title:
--   Bad Share: trace coind mul card
-- statement:
--   The Bad Share construction uses the trace coind mul card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TraceCompLeftFunLeft.lean#L48-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/TraceCompLeftFunLeft.lean#L48-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TraceCompLeftFunLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
noncomputable section
open GlobalTheory GlobalTheory.BadShare
variable {G : Type} [Group G] [Fintype G] {Γ : Type} [Group Γ] [Fintype Γ] (r : Γ →* G)
  {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ Γ W)

theorem GlobalTheory.BadShare.trace_coind_mul_card (g : G) :
    LinearMap.trace ℂ _ (Representation.coind r σ g) * (Fintype.card Γ : ℂ) =
      ∑ γ : Γ, ∑ x : G, if r γ * (x * g) = x then LinearMap.trace ℂ W (σ γ⁻¹) else 0 := by sorry
