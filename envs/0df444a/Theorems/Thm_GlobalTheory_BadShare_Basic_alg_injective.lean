-- Prove2me | Theorems.Thm_GlobalTheory_BadShare_Basic_alg_injective
-- name    : GlobalTheory.BadShare.Basic.alg_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:21:31.303769+00:00
-- url     : https://prove2.me/theorems/e0ce087e-f97f-4cba-87f0-46bd8237d4e9
-- title:
--   Basic: alg injective
-- statement:
--   The Basic construction uses the alg injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L307-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/StandardFiveNontrivial.lean#L307-L308

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

theorem GlobalTheory.BadShare.Basic.alg_injective : Function.Injective (alg : (G → ℂ) → MonoidAlgebra ℂ G) := by sorry
