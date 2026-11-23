-- Prove2me | Theorems.Thm_GlobalTheory_mem_span_first_columns_iff
-- name    : GlobalTheory.mem_span_first_columns_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:30.33272+00:00
-- url     : https://prove2.me/theorems/8d34dcc7-b116-4fee-a092-5bebcc0b69fe
-- title:
--   Global Theory: mem span first columns iff
-- statement:
--   The Global Theory construction uses the mem span first columns iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsTriangularOfSpanFirstColumnsLe.lean#L7-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsTriangularOfSpanFirstColumnsLe.lean#L7-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsTriangularOfSpanFirstColumnsLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix

theorem GlobalTheory.mem_span_first_columns_iff {R : Type} [CommRing R] {n r : ℕ}
    (M : Matrix (Fin n) (Fin r) R) (k : ℕ) (x : Fin n → R) :
    x ∈ Submodule.span R {y : Fin n → R | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => M i j} ↔
      ∃ c : Fin r → R, (∀ j : Fin r, k ≤ (j : ℕ) → c j = 0) ∧ x = M *ᵥ c := by sorry
