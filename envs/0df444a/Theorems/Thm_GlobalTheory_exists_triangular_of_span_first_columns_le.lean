-- Prove2me | Theorems.Thm_GlobalTheory_exists_triangular_of_span_first_columns_le
-- name    : GlobalTheory.exists_triangular_of_span_first_columns_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:41:57.259989+00:00
-- url     : https://prove2.me/theorems/e9b9497a-393c-432b-9001-41ea8d7e75c8
-- title:
--   Global Theory: exists triangular of span first columns le
-- statement:
--   The Global Theory construction uses the exists triangular of span first columns le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsTriangularOfSpanFirstColumnsLe.lean#L40-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsTriangularOfSpanFirstColumnsLe.lean#L40-L54

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

theorem GlobalTheory.exists_triangular_of_span_first_columns_le {R : Type} [CommRing R] {n r : ℕ}
    (u u' : Matrix (Fin n) (Fin r) R)
    (h : ∀ k : ℕ,
      Submodule.span R {y : Fin n → R | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => u' i j} ≤
      Submodule.span R {y : Fin n → R | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => u i j}) :
    ∃ b : Matrix (Fin r) (Fin r) R, b.BlockTriangular id ∧ u' = u * b := by sorry
