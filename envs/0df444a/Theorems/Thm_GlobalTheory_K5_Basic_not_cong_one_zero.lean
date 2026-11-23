-- Prove2me | Theorems.Thm_GlobalTheory_K5_Basic_not_cong_one_zero
-- name    : GlobalTheory.K5.Basic.not_cong_one_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:15:06.698445+00:00
-- url     : https://prove2.me/theorems/8b7b3761-9b41-4b5a-ac93-0c4f977f5215
-- title:
--   Basic: not cong one zero
-- statement:
--   The Basic construction uses the not cong one zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L410-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/NotCoboundaryConstantOne.lean#L410-L418

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K5 GlobalTheory.K5.Basic
open Polynomial
variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

theorem GlobalTheory.K5.Basic.not_cong_one_zero (h : IsClo p Ω) (k : ℕ) (hk : k ≠ 0) : ¬ Cong p k (1 : Ω) 0 := by sorry
