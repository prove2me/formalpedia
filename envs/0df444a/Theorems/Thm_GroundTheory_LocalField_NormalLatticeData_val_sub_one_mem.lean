-- Prove2me | Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_val_sub_one_mem
-- name    : GroundTheory.LocalField.NormalLatticeData.val_sub_one_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:10:15.048456+00:00
-- url     : https://prove2.me/theorems/83141cee-561a-4ab9-8956-9a6221fd631a
-- title:
--   Normal Lattice Data: val sub one mem
-- statement:
--   The Normal Lattice Data construction uses the val sub one mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L181-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L181-L181

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

theorem GroundTheory.LocalField.NormalLatticeData.val_sub_one_mem (x : D.units 0) : D.val x - 1 ∈ D.lat D.k := by sorry
