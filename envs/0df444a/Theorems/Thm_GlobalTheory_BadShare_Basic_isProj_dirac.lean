-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_Basic_isProj_dirac
-- name    : GlobalTheory.BadShare.Basic.isProj_dirac
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:00:04.975882+00:00
-- url     : https://prove2.me/theorems/900468b5-635e-41f3-93d1-56827e09941f
-- title:
--   Basic: is Proj dirac
-- statement:
--   The Basic construction uses the is Proj dirac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L481-L488
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L481-L488

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

theorem GlobalTheory.BadShare.Basic.isProj_dirac {G : Type} [Group G] [Fintype G] : IsProj (dirac : G → ℂ) := by sorry
