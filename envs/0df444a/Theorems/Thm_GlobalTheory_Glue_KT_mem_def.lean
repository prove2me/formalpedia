-- Prove2me | Theorems.Thm_GlobalTheory_Glue_KT_mem_def
-- name    : GlobalTheory.Glue.KT.mem_def
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:03.052488+00:00
-- url     : https://prove2.me/theorems/b2ae899b-b78a-5799-950a-5f0ceb8aa551
-- title:
--   KT: mem def
-- statement:
--   The KT construction uses the mem def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ApplyEqOfMemAdjoin.lean#L94-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ApplyEqOfMemAdjoin.lean#L94-L94

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

theorem GlobalTheory.Glue.KT.mem_def (X : GlobalTheory.KZ.Tower Ω ε) (L : ℕ) (f : X.K) : f ∈ KT X L ↔ X.sl (ofSL (ModularGroup.T ^ L)) f = f := by sorry
