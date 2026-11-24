-- Prove2me | Theorems.Thm_GlobalTheory_SmulMemOfMemSpan_main
-- name    : GlobalTheory.SmulMemOfMemSpan.main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:58.441184+00:00
-- url     : https://prove2.me/theorems/11f3608f-7acd-41c2-bb4c-791ab3fc75ed
-- title:
--   Smul Mem Of Mem Span: main
-- statement:
--   The Smul Mem Of Mem Span construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/Imports.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/Imports.lean#L30-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SmulMemOfMemSpan

theorem GlobalTheory.SmulMemOfMemSpan.main : ∀ {R K V : Type} [inst : CommRing R] [IsDomain R] [inst_2 : Field K] [inst_3 : Algebra R K] [IsFractionRing R K] [inst_5 : AddCommGroup V] [inst_6 : Module R V] [inst_7 : Module K V] [IsScalarTower R K V] (M : Submodule R V) {v : V}, v ∈ Submodule.span K (↑M : Set V) → ∃ (a : R), a ≠ (0 : R) ∧ a • v ∈ M := by sorry
