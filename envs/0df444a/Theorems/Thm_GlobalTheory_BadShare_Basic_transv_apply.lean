-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_Basic_transv_apply
-- name    : GlobalTheory.BadShare.Basic.transv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:30.221558+00:00
-- url     : https://prove2.me/theorems/29640533-62d1-467a-a520-c212446cc1a1
-- title:
--   Basic: transv apply
-- statement:
--   The Basic construction uses the transv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L242-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L242-L244

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

theorem GlobalTheory.BadShare.Basic.transv_apply (a b : Fin N) (h : a ≠ b) (i j : Fin N) :
    (transv (g := g) a b h).val i j = (if i = j then 1 else 0) + (if a = i ∧ b = j then 1 else 0) := by sorry
