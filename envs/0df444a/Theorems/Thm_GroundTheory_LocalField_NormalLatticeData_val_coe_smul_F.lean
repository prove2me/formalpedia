-- Prove2me | Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_val_coe_smul_F
-- name    : GroundTheory.LocalField.NormalLatticeData.val_coe_smul_F
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:10:31.918119+00:00
-- url     : https://prove2.me/theorems/1d96f7c1-3a4d-48e4-94f2-345af62826dd
-- title:
--   Normal Lattice Data: val coe smul F
-- statement:
--   The Normal Lattice Data construction uses the val coe smul F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L297-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L297-L299

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

theorem GroundTheory.LocalField.NormalLatticeData.val_coe_smul_F {j : ℕ} (σ : Gal(L/K)) (y : D.filt.F j) :
    D.val ((σ • y : D.filt.F j) : D.units 0) = σ (D.val y) := by sorry
