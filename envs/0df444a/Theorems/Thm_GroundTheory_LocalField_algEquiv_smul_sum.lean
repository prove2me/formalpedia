-- Prove2me | Theorems.Thm_GroundTheory_LocalField_algEquiv_smul_sum
-- name    : GroundTheory.LocalField.algEquiv_smul_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:16.664834+00:00
-- url     : https://prove2.me/theorems/c163b6d8-dd27-4028-a27a-c90ba86ab6e0
-- title:
--   Local Field: alg Equiv smul sum
-- statement:
--   The Local Field construction uses the alg Equiv smul sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L81-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L81-L88

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

theorem GroundTheory.LocalField.algEquiv_smul_sum (τ : Gal(L/K)) (s : ℕ) (c : Gal(L/K) → 𝒪[K]) :
    τ (π ^ s • ∑ σ, c σ • σ θ) = π ^ s • ∑ σ, c (τ⁻¹ * σ) • σ θ := by sorry
