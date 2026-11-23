-- Prove2me | Theorems.Thm_GroundTheory_LocalField_smul_sum_mem_normalLattice_add_iff
-- name    : GroundTheory.LocalField.smul_sum_mem_normalLattice_add_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:18:02.063115+00:00
-- url     : https://prove2.me/theorems/98e65065-e952-407a-8f36-d84f8951f9a1
-- title:
--   Local Field: smul sum mem normal Lattice add iff
-- statement:
--   The Local Field construction uses the smul sum mem normal Lattice add iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L49-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L49-L65

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

theorem GroundTheory.LocalField.smul_sum_mem_normalLattice_add_iff (hπ : π ≠ 0)
    (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) (s N : ℕ) (c : Gal(L/K) → 𝒪[K]) :
    π ^ s • ∑ σ, c σ • σ θ ∈ normalLattice π θ (s + N) ↔ ∀ σ, π ^ N ∣ c σ := by sorry
