-- Prove2me | Theorems.Thm_GroundTheory_LocalField_residueDegree_eq_finrank
-- name    : GroundTheory.LocalField.residueDegree_eq_finrank
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:44.743796+00:00
-- url     : https://prove2.me/theorems/0874c86a-10f5-4468-80f7-825a4e182c19
-- title:
--   Local Field: residue Degree eq finrank
-- statement:
--   The Local Field construction uses the residue Degree eq finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Integers.lean#L152-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Integers.lean#L152-L153

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

theorem GroundTheory.LocalField.residueDegree_eq_finrank : residueDegree K L = Module.finrank 𝓀[K] 𝓀[L] := by sorry
