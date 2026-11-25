-- Prove2me | Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_isOpen_units
-- name    : GroundTheory.LocalField.NormalLatticeData.isOpen_units
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T01:13:35.650928+00:00
-- url     : https://prove2.me/theorems/26d12ac2-0a86-4ff7-a9d9-a94f4f6a66f2
-- title:
--   Normal Lattice Data: is Open units
-- statement:
--   The Normal Lattice Data construction uses the is Open units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L449-L454
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L449-L454

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
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L]
open GroundTheory.LocalField.NormalLatticeData
variable (D : NormalLatticeData K L)

theorem GroundTheory.LocalField.NormalLatticeData.isOpen_units (j : ℕ) : IsOpen (D.units j : Set 𝒪[L]ˣ) := by sorry
