-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mul_mem_normalLattice_succ
-- name    : GroundTheory.LocalField.mul_mem_normalLattice_succ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:59.101783+00:00
-- url     : https://prove2.me/theorems/7b7e11bf-96f3-4bcc-b173-13f3421a9b8e
-- title:
--   Local Field: mul mem normal Lattice succ
-- statement:
--   The Local Field construction uses the mul mem normal Lattice succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L200-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L200-L207

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

theorem GroundTheory.LocalField.mul_mem_normalLattice_succ {r : ℕ}
    (hr : ∀ σ τ : Gal(L/K), π ^ r • (σ θ * τ θ) ∈ normalLattice π θ 0) {s t : ℕ} (hs : r < s)
    {x y : L} (hx : x ∈ normalLattice π θ s) (hy : y ∈ normalLattice π θ t) :
    x * y ∈ normalLattice π θ (t + 1) := by sorry
