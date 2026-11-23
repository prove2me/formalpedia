-- Prove2me | Theorems.Thm_GroundTheory_LocalField_algEquiv_mem_normalLattice
-- name    : GroundTheory.LocalField.algEquiv_mem_normalLattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:14.770403+00:00
-- url     : https://prove2.me/theorems/5e9e16bd-4684-4c15-8866-bf3b42af09e0
-- title:
--   Local Field: alg Equiv mem normal Lattice
-- statement:
--   The Local Field construction uses the alg Equiv mem normal Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L90-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L90-L94

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

theorem GroundTheory.LocalField.algEquiv_mem_normalLattice (τ : Gal(L/K)) {s : ℕ} {x : L} (hx : x ∈ normalLattice π θ s) :
    τ x ∈ normalLattice π θ s := by sorry
