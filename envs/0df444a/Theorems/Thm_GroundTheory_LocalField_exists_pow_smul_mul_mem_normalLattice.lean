-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_pow_smul_mul_mem_normalLattice
-- name    : GroundTheory.LocalField.exists_pow_smul_mul_mem_normalLattice
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:44:16.225524+00:00
-- url     : https://prove2.me/theorems/f1671f5b-e2f9-49ff-856e-f5ba47a218e8
-- title:
--   Local Field: exists pow smul mul mem normal Lattice
-- statement:
--   The Local Field construction uses the exists pow smul mul mem normal Lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L166-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L166-L171

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
variable [IsGalois K L]
omit [ValuativeRel L] [ValuativeExtension K L]

theorem GroundTheory.LocalField.exists_pow_smul_mul_mem_normalLattice (hπ : Irreducible π)
    (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) :
    ∃ r, ∀ σ τ : Gal(L/K), π ^ r • (σ θ * τ θ) ∈ normalLattice π θ 0 := by sorry
