-- Prove2me | Theorems.Thm_GroundTheory_LocalField_finiteExtensionStructure_isNonarchimedeanLocalField
-- name    : GroundTheory.LocalField.finiteExtensionStructure_isNonarchimedeanLocalField
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:01.33168+00:00
-- url     : https://prove2.me/theorems/20b6375d-65f1-4fb9-8cd4-16479aa739eb
-- title:
--   Local Field: finite Extension Structure is Nonarchimedean Local Field
-- statement:
--   The Local Field construction uses the finite Extension Structure is Nonarchimedean Local Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FiniteExtension.lean#L129-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FiniteExtension.lean#L129-L148

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
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
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.finiteExtensionStructure_isNonarchimedeanLocalField :
    letI := (finiteExtensionStructure K L).rel
    letI := (finiteExtensionStructure K L).top
    IsNonarchimedeanLocalField L := by sorry
