-- Prove2me | Theorems.Thm_GlobalTheory_Glue_IsNTr_unique
-- name    : GlobalTheory.Glue.IsNTr.unique
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:13:05.846255+00:00
-- url     : https://prove2.me/theorems/467fd3ff-9ce2-41d8-925e-7508720c2bfd
-- title:
--   Is NTr: unique
-- statement:
--   The Is NTr construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ApplyEqOfMemAdjoin.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ApplyEqOfMemAdjoin.lean#L75-L80

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_EeProd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_ApplyEqOfMemAdjoin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped MatrixGroups
open GlobalTheory GlobalTheory.Glue
open GlobalTheory.KZ GlobalTheory.K5
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
variable {p : ℕ} [Fact p.Prime] {Ωl : Type} [Field Ωl] [Algebra (O0 p) Ωl]

theorem GlobalTheory.Glue.IsNTr.unique {l n m : ℕ} [NeZero l] {F F' F'' : Ω} (h : IsNTr ε l n m F F') (h' : IsNTr ε l n m F F'') : F' = F'' := by sorry
