-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_Basic_finrank_pos_of_countAt
-- name    : GlobalTheory.BadShare.Basic.finrank_pos_of_countAt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:29.439985+00:00
-- url     : https://prove2.me/theorems/ae444f36-7b0e-44f1-b5ca-ec2ca209b940
-- title:
--   Basic: finrank pos of count At
-- statement:
--   The Basic construction uses the finrank pos of count At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L490-L506
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L490-L506

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

theorem GlobalTheory.BadShare.Basic.finrank_pos_of_countAt {g₁ g₂ N : ℕ} [Fact g₁.Prime] [Fact g₂.Prime] {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    {M : Type} [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ ((ι₁ → GG g₁ N) × (ι₂ → GG g₂ N)) M) {ep : ℝ}
    (hep : ep < 1) (h : CountAt ρ ep) : 0 < Module.finrank ℂ M := by sorry
