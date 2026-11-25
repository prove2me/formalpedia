-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_Basic_countAt_of_trace_eq_zero
-- name    : GlobalTheory.BadShare.Basic.countAt_of_trace_eq_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:12.204112+00:00
-- url     : https://prove2.me/theorems/98d96c65-ea12-536f-80f2-e1e2673f872d
-- title:
--   Basic: count At of trace eq zero
-- statement:
--   The Basic construction uses the count At of trace eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L420-L434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L420-L434

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_StandardFiveNontrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Classical
open GlobalTheory GlobalTheory.BadShare
variable (g : ℕ) [Fact g.Prime] (N : ℕ)
variable {g N}
open GlobalTheory.BadShare.Basic

theorem GlobalTheory.BadShare.Basic.countAt_of_trace_eq_zero {g₁ g₂ N : ℕ} [Fact g₁.Prime] [Fact g₂.Prime] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] [Nontrivial M]
    (ρ : Representation ℂ ((ι₁ → GG g₁ N) × (ι₂ → GG g₂ N)) M)
    (h : ∀ γ, γ ≠ 1 → AllUnip γ.1 ∨ AllUnip γ.2 → LinearMap.trace ℂ M (ρ γ) = 0) : CountAt ρ 0 := by sorry
