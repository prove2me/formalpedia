-- Prove2me | Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_grHom_eq_one_iff
-- name    : GroundTheory.LocalField.NormalLatticeData.grHom_eq_one_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:10:48.856827+00:00
-- url     : https://prove2.me/theorems/ab01686c-7fd0-4fd4-a453-7208b8ca93a3
-- title:
--   Normal Lattice Data: gr Hom eq one iff
-- statement:
--   The Normal Lattice Data construction uses the gr Hom eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L291-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L291-L295

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

theorem GroundTheory.LocalField.NormalLatticeData.grHom_eq_one_iff {j : ℕ} (x : D.filt.F j) :
    D.grHom j x = 1 ↔ (x : D.units 0) ∈ D.filt.F (j + 1) := by sorry
