-- Prove2me | Theorems.Thm_GlobalTheory_NonzeroScalarInSpan_exists_ne_zero_smul_mem_of_mem_span
-- name    : GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T02:46:35.603924+00:00
-- url     : https://prove2.me/theorems/ad7d5884-6542-4b17-81eb-7fd316da963b
-- title:
--   Nonzero Scalar In Span: exists ne zero smul mem of mem span
-- statement:
--   The Nonzero Scalar In Span construction uses the exists ne zero smul mem of mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroSmulMemOfMemSpan.lean#L5-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroSmulMemOfMemSpan.lean#L5-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroSmulMemOfMemSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NonzeroScalarInSpan

theorem GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span {R K V : Type} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (N : Submodule R V) {x : V}
    (hx : x ∈ Submodule.span K (↑N : Set V)) : ∃ a : R, a ≠ 0 ∧ a • x ∈ N := by sorry
