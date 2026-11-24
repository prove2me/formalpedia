-- Prove2me | Theorems.Thm_GroundTheory_LocalField_mul_mem_normalLattice
-- name    : GroundTheory.LocalField.mul_mem_normalLattice
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:44:47.734796+00:00
-- url     : https://prove2.me/theorems/11a398b1-a15d-406e-8ec6-858f937374d0
-- title:
--   Local Field: mul mem normal Lattice
-- statement:
--   The Local Field construction uses the mul mem normal Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L179-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L179-L198

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

theorem GroundTheory.LocalField.mul_mem_normalLattice {r : ℕ}
    (hr : ∀ σ τ : Gal(L/K), π ^ r • (σ θ * τ θ) ∈ normalLattice π θ 0) {a b : ℕ} {x y : L}
    (hx : x ∈ normalLattice π θ (a + r)) (hy : y ∈ normalLattice π θ b) :
    x * y ∈ normalLattice π θ (a + b) := by sorry
