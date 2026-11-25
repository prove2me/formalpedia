-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_Basic_isProj_tens2
-- name    : GlobalTheory.BadShare.Basic.isProj_tens2
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:56:42.07881+00:00
-- url     : https://prove2.me/theorems/6214c39b-44d1-424d-91de-b2f539b8f8bc
-- title:
--   Basic: is Proj tens2
-- statement:
--   The Basic construction uses the is Proj tens2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L407-L410
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L407-L410

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
variable {G : Type} [Group G] [Fintype G]

theorem GlobalTheory.BadShare.Basic.isProj_tens2 {G' : Type} [Group G'] [Fintype G'] {a : G → ℂ} {b : G' → ℂ} (ha : IsProj a) (hb : IsProj b) :
    IsProj (tens2 a b) := by sorry
