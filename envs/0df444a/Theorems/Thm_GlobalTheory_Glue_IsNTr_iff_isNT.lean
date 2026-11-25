-- Prove2me | Theorems.Thm_GlobalTheory_Glue_IsNTr_iff_isNT
-- name    : GlobalTheory.Glue.IsNTr.iff_isNT
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:19.001053+00:00
-- url     : https://prove2.me/theorems/546e2d93-cb6f-50b4-805c-142e88f44a16
-- title:
--   Is NTr: iff is NT
-- statement:
--   The Is NTr construction uses the iff is NT property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ApplyEqOfMemAdjoin.lean#L62-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ApplyEqOfMemAdjoin.lean#L62-L64

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

theorem GlobalTheory.Glue.IsNTr.iff_isNT {l n m : ℕ} [NeZero l] {F F' : Ω} (hm : 1 ≤ m) (hmn : m ≤ n) (hF : InZl ε l n F) :
    IsNTr ε l n m F F' ↔ IsNT ε l n m F F' := by sorry
