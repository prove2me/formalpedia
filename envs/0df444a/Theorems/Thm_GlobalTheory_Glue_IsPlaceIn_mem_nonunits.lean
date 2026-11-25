-- Prove2me | Theorems.Thm_GlobalTheory_Glue_IsPlaceIn_mem_nonunits
-- name    : GlobalTheory.Glue.IsPlaceIn.mem_nonunits
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:49.46096+00:00
-- url     : https://prove2.me/theorems/bc399bbc-cbcb-4f93-a54a-18195d4d2979
-- title:
--   Is Place In: mem nonunits
-- statement:
--   The Is Place In construction uses the mem nonunits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ApplyEqOfMemAdjoin.lean#L111-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/ApplyEqOfMemAdjoin.lean#L111-L117

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

theorem GlobalTheory.Glue.IsPlaceIn.mem_nonunits (hc : IsClo p Ωl) {A : ValuationSubring Ω} {T : GlobalTheory.K5.Tower p Ωl} {j : Ω →+* Ωl}
    (h : IsPlaceIn ε A T j) : ((p : ℕ) : Ω) ∈ A.nonunits := by sorry
