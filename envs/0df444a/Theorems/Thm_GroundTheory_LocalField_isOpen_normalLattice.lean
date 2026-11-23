-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isOpen_normalLattice
-- name    : GroundTheory.LocalField.isOpen_normalLattice
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:41.121914+00:00
-- url     : https://prove2.me/theorems/f234010d-8b68-4dde-a8a7-d8e126f84e61
-- title:
--   Local Field: is Open normal Lattice
-- statement:
--   The Local Field construction uses the is Open normal Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L410-L444
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L410-L444

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
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [IsGalois K L]
variable (π : 𝒪[K]) (θ : L)

theorem GroundTheory.LocalField.isOpen_normalLattice (hπ : Irreducible π) (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ)
    (s : ℕ) : IsOpen (normalLattice π θ s : Set L) := by sorry
