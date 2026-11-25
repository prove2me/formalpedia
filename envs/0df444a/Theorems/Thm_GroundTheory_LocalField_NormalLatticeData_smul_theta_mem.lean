-- Prove2me | Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_smul_theta_mem
-- name    : GroundTheory.LocalField.NormalLatticeData.smul_theta_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:14:07.230461+00:00
-- url     : https://prove2.me/theorems/3407ea22-6ff8-46a1-ac53-abb039242ca6
-- title:
--   Normal Lattice Data: smul theta mem
-- statement:
--   The Normal Lattice Data construction uses the smul theta mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L304-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L304-L306

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivialLocal
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
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
open GroundTheory.LocalField.NormalLatticeData
variable (D : NormalLatticeData K L)
attribute [local instance] action
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeExtension K L]
  [FiniteDimensional K L]

theorem GroundTheory.LocalField.NormalLatticeData.smul_theta_mem (j : ℕ) (c : 𝒪[K]) : c • D.π ^ (D.k + j) • D.θ ∈ D.lat (D.k + j) := by sorry
