-- Prove2me | Theorems.Thm_GlobalTheory_Glue_InZl_mem_adjoin
-- name    : GlobalTheory.Glue.InZl.mem_adjoin
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:56:52.816269+00:00
-- url     : https://prove2.me/theorems/d7f93504-630c-447d-8988-7fd056ebc3d0
-- title:
--   In Zl: mem adjoin
-- statement:
--   The In Zl construction uses the mem adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ApplyEqOfMemAdjoin.lean#L50-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ApplyEqOfMemAdjoin.lean#L50-L60

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

theorem GlobalTheory.Glue.InZl.mem_adjoin {l n : ℕ} {F : Ω} (h : InZl ε l n F) : F ∈ IntermediateField.adjoin ℚ {zt ε l n} := by sorry
