-- Prove2me | Theorems.Thm_GlobalTheory_offDiagonal_matrixUnits_irreducible
-- name    : GlobalTheory.offDiagonal_matrixUnits_irreducible
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:13:04.829816+00:00
-- url     : https://prove2.me/theorems/147db975-bdb9-4446-9d00-44db8962ff88
-- title:
--   Global Theory: off Diagonal matrix Units irreducible
-- statement:
--   The Global Theory construction uses the off Diagonal matrix Units irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/OffDiagonalMatrixUnitsIrreducible.lean#L8-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/OffDiagonalMatrixUnitsIrreducible.lean#L8-L59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_OffDiagonalMatrixUnitsIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory

theorem GlobalTheory.offDiagonal_matrixUnits_irreducible :
    (∀ (r p : ℕ), 0 < p → p < r → ∀ W : Submodule ℂ (Fin r → ℂ),
      (∀ j k : Fin r, (j : ℕ) < p → p ≤ (k : ℕ) → ∀ v ∈ W,
        (Matrix.single j k (1 : ℂ)).mulVec v ∈ W ∧ (Matrix.single k j (1 : ℂ)).mulVec v ∈ W) →
      W = ⊥ ∨ W = ⊤) := by sorry
