-- Prove2me | Theorems.Thm_GlobalTheory_cell_columns_saturated_and_triangular
-- name    : GlobalTheory.cell_columns_saturated_and_triangular
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:07:46.428412+00:00
-- url     : https://prove2.me/theorems/a3e72dbc-5887-48f1-8850-60213f3369e2
-- title:
--   Global Theory: cell columns saturated and triangular
-- statement:
--   The Global Theory construction uses the cell columns saturated and triangular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsTriangularOfSpanFirstColumnsLe.lean#L56-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/ExistsTriangularOfSpanFirstColumnsLe.lean#L56-L118

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

theorem GlobalTheory.cell_columns_saturated_and_triangular :
    ∀ (V L : Type) [CommRing V] [IsDomain V] [Field L] [Algebra V L] [IsFractionRing V L] (n r : ℕ) (ι : Fin r ↪ Fin n) (u : Matrix (Fin n) (Fin r) V), (∀ i j : Fin r, i < j → u (ι i) j = 0) ∧ (∀ i : Fin r, u (ι i) i = 1) → (∀ (k : ℕ) (x : Fin n → V), (fun i => algebraMap V L (x i)) ∈ Submodule.span L {y : Fin n → L | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => algebraMap V L (u i j)} ↔ x ∈ Submodule.span V {y : Fin n → V | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => u i j}) ∧ ∀ u' : Matrix (Fin n) (Fin r) V, (∀ k : ℕ, Submodule.span V {y : Fin n → V | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => u' i j} = Submodule.span V {y : Fin n → V | ∃ j : Fin r, (j : ℕ) < k ∧ y = fun i => u i j}) → ∃ b : Matrix (Fin r) (Fin r) V, b.BlockTriangular id ∧ (∀ i, IsUnit (b i i)) ∧ u' = u * b := by sorry
