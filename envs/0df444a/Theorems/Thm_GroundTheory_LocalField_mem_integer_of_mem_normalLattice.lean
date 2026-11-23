-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_integer_of_mem_normalLattice
-- name    : GroundTheory.LocalField.mem_integer_of_mem_normalLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:03.742815+00:00
-- url     : https://prove2.me/theorems/7a8aa700-4ff9-49b6-82c8-276fcb4a911d
-- title:
--   Local Field: mem integer of mem normal Lattice
-- statement:
--   The Local Field construction uses the mem integer of mem normal Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L107-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L107-L113

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
  [ValuativeExtension K L]
variable (π : 𝒪[K]) (θ : L)
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.mem_integer_of_mem_normalLattice (hθO : ∀ σ : Gal(L/K), σ θ ∈ 𝒪[L]) {s : ℕ} {x : L}
    (hx : x ∈ normalLattice π θ s) : x ∈ 𝒪[L] := by sorry
