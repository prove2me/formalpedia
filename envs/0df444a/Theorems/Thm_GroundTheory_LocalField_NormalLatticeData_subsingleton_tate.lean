-- Prove2me | Theorems.Thm_GroundTheory_LocalField_NormalLatticeData_subsingleton_tate
-- name    : GroundTheory.LocalField.NormalLatticeData.subsingleton_tate
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T01:13:42.407528+00:00
-- url     : https://prove2.me/theorems/d93e9905-f3ca-4a3a-98d6-9a9b2230a365
-- title:
--   Normal Lattice Data: subsingleton tate
-- statement:
--   The Normal Lattice Data construction uses the subsingleton tate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L460-L463
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompleteTrivialLocal.lean#L460-L463

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
attribute [local instance] action
omit [TopologicalSpace L] [IsNonarchimedeanLocalField L] [IsGalois K L]

theorem GroundTheory.LocalField.NormalLatticeData.subsingleton_tate :
    Subsingleton (TateZero Gal(L/K) (D.units 0)) ∧ Subsingleton (TateNegOne Gal(L/K) (D.units 0)) := by sorry
