-- Prove2me | Theorems.Thm_GlobalTheory_Glue_IsExpIn_par
-- name    : GlobalTheory.Glue.IsExpIn.par
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:23.358001+00:00
-- url     : https://prove2.me/theorems/9258999d-e15b-5bd5-84e4-3ed926344ba6
-- title:
--   Is Exp In: par
-- statement:
--   The Is Exp In construction uses the par property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ApplyEqOfMemAdjoin.lean#L147-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ApplyEqOfMemAdjoin.lean#L147-L147

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

theorem GlobalTheory.Glue.IsExpIn.par (h : IsExpIn X A T j n ψ io) : ψ (qO p) = T.qq n := by sorry
