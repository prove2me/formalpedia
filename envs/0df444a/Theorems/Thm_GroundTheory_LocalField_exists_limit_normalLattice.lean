-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_limit_normalLattice
-- name    : GroundTheory.LocalField.exists_limit_normalLattice
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:11.263789+00:00
-- url     : https://prove2.me/theorems/801cdc87-e895-41c4-bb19-96f24a58d972
-- title:
--   Local Field: exists limit normal Lattice
-- statement:
--   The Local Field construction uses the exists limit normal Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L271-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L271-L290

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (π : 𝒪[K]) (θ : L)

theorem GroundTheory.LocalField.exists_limit_normalLattice (hπ : Irreducible π)
    (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) {s : ℕ} (y : ℕ → L)
    (hy : ∀ n, y n ∈ normalLattice π θ s)
    (hc : ∀ N, ∃ M, ∀ m ≥ M, ∀ n ≥ M, y n - y m ∈ normalLattice π θ (s + N)) :
    ∃ z ∈ normalLattice π θ s, ∀ N, ∃ M, ∀ n ≥ M, y n - z ∈ normalLattice π θ (s + N) := by sorry
