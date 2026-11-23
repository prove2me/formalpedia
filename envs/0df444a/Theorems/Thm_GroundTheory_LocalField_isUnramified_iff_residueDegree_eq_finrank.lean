-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isUnramified_iff_residueDegree_eq_finrank
-- name    : GroundTheory.LocalField.isUnramified_iff_residueDegree_eq_finrank
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:17:54.36287+00:00
-- url     : https://prove2.me/theorems/aad3ca37-0933-4b1f-9f2d-728009ff0abc
-- title:
--   Local Field: is Unramified iff residue Degree eq finrank
-- statement:
--   The Local Field construction uses the is Unramified iff residue Degree eq finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedDefs.lean#L32-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedDefs.lean#L32-L43

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
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
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.isUnramified_iff_residueDegree_eq_finrank :
    IsUnramified K L ↔ residueDegree K L = Module.finrank K L := by sorry
