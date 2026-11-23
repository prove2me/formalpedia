-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mem_normalLattice_iff
-- name    : GroundTheory.LocalField.mem_normalLattice_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:31.577991+00:00
-- url     : https://prove2.me/theorems/c73fab80-8c70-484d-a7d6-8d9ce7d98557
-- title:
--   Local Field: mem normal Lattice iff
-- statement:
--   The Local Field construction uses the mem normal Lattice iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L32-L35

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
variable (π : 𝒪[K]) (θ : L)

theorem GroundTheory.LocalField.mem_normalLattice_iff {s : ℕ} {x : L} :
    x ∈ normalLattice π θ s ↔ ∃ c : Gal(L/K) → 𝒪[K], π ^ s • ∑ σ, c σ • σ θ = x := by sorry
