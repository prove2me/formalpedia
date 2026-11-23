-- Prove2me | Theorems.Thm_GroundTheory_LocalField_smul_sum_sub_smul_sum
-- name    : GroundTheory.LocalField.smul_sum_sub_smul_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:22.7661+00:00
-- url     : https://prove2.me/theorems/1c7c73fa-70f4-40e6-ac6c-ed1d70aa14b1
-- title:
--   Local Field: smul sum sub smul sum
-- statement:
--   The Local Field construction uses the smul sum sub smul sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L259-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/NormalLattice.lean#L259-L261

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
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.smul_sum_sub_smul_sum (s : ℕ) (c d : Gal(L/K) → 𝒪[K]) :
    π ^ s • ∑ σ, c σ • σ θ - π ^ s • ∑ σ, d σ • σ θ = π ^ s • ∑ σ, (c σ - d σ) • σ θ := by sorry
