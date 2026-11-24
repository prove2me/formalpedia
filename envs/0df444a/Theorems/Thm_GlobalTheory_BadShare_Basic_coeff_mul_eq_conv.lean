-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_Basic_coeff_mul_eq_conv
-- name    : GlobalTheory.BadShare.Basic.coeff_mul_eq_conv
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T10:59:58.029997+00:00
-- url     : https://prove2.me/theorems/0162e81e-06f9-41c3-b0f8-2ba844a5f049
-- title:
--   Basic: coeff mul eq conv
-- statement:
--   The Basic construction uses the coeff mul eq conv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L310-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L310-L314

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

theorem GlobalTheory.BadShare.Basic.coeff_mul_eq_conv (a b : MonoidAlgebra ℂ G) (x : G) :
    (a * b).coeff x = conv (fun y => a.coeff y) (fun y => b.coeff y) x := by sorry
