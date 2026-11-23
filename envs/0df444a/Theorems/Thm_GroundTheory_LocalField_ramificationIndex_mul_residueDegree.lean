-- Prove2me | Theorems.Thm_GroundTheory_LocalField_ramificationIndex_mul_residueDegree
-- name    : GroundTheory.LocalField.ramificationIndex_mul_residueDegree
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:33.348372+00:00
-- url     : https://prove2.me/theorems/d1a98660-f9a3-48f3-8dea-cfd4af2e3bf8
-- title:
--   Local Field: ramification Index mul residue Degree
-- statement:
--   The Local Field construction uses the ramification Index mul residue Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Integers.lean#L123-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Integers.lean#L123-L128

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Integers
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
open ValuativeRel
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]
variable [FiniteDimensional K L]

theorem GroundTheory.LocalField.ramificationIndex_mul_residueDegree :
    ramificationIndex K L * residueDegree K L = Module.finrank K L := by sorry
