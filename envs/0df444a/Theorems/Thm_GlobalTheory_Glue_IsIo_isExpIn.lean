-- Prove2me | Theorems.Thm_GlobalTheory_Glue_IsIo_isExpIn
-- name    : GlobalTheory.Glue.IsIo.isExpIn
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:02.35652+00:00
-- url     : https://prove2.me/theorems/6a29d914-2326-4e03-aefd-a420d77df97b
-- title:
--   Is Io: is Exp In
-- statement:
--   The Is Io construction uses the is Exp In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ApplyEqOfMemAdjoin.lean#L141-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ApplyEqOfMemAdjoin.lean#L141-L142

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
variable {X : GlobalTheory.KZ.Tower Ω ε} {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl} {n : ℕ} {ψ : O0 p →+* Ωl}
  {io : KT X (p ^ n) →+* Ωl}

theorem GlobalTheory.Glue.IsIo.isExpIn (h : IsIo X A T j n ψ io) (hj : IsPlaceIn ε A T j) (hψ : IsReb T n ψ) : IsExpIn X A T j n ψ io := by sorry
