-- Prove2me | Theorems.Thm_GlobalTheory_matrix_integers_mod_nat_finite
-- name    : GlobalTheory.matrix_integers_mod_nat_finite
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:24.277328+00:00
-- url     : https://prove2.me/theorems/5b1cd5fa-f718-457e-9d44-e0950d4a2d5d
-- title:
--   Global Theory: matrix integers mod nat finite
-- statement:
--   The Global Theory construction uses the matrix integers mod nat finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MatrixIntegersModNatFinite.lean#L34-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MatrixIntegersModNatFinite.lean#L34-L47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
open GlobalTheory

theorem GlobalTheory.matrix_integers_mod_nat_finite : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (Y Y' : Type) [Fintype Y] [Fintype Y'] (n : ℕ), 0 < n →
    ∃ R : Set (Matrix Y Y' k), R.Finite ∧ ∀ t : Matrix Y Y' k, (∀ r q, t r q ∈ 𝒪[k]) →
      ∃ s ∈ R, ∃ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) ∧ t = s + n • u := by sorry
