-- Prove2me | Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_div_mem_filt_iff
-- name    : GroundTheory.LocalField.NormalLatticeData.div_mem_filt_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:10:59.0048+00:00
-- url     : https://prove2.me/theorems/cbab2361-6ce6-4f85-a766-ff66a86f8c3f
-- title:
--   Normal Lattice Data: div mem filt iff
-- statement:
--   The Normal Lattice Data construction uses the div mem filt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L201-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L201-L216

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

theorem GroundTheory.LocalField.NormalLatticeData.div_mem_filt_iff {j : ℕ} {x y : D.units 0} :
    x / y ∈ D.filt.F j ↔ D.val x - D.val y ∈ D.lat (D.k + j) := by sorry
