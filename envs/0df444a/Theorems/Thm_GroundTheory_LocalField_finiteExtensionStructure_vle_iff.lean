-- Prove2me | Theorems.Thm_GroundTheory_LocalField_finiteExtensionStructure_vle_iff
-- name    : GroundTheory.LocalField.finiteExtensionStructure_vle_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:45:00.722723+00:00
-- url     : https://prove2.me/theorems/20aa273d-c7a7-4e3c-a1bc-08d7706b9ac2
-- title:
--   Local Field: finite Extension Structure vle iff
-- statement:
--   The Local Field construction uses the finite Extension Structure vle iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FiniteExtension.lean#L110-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FiniteExtension.lean#L110-L114

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

theorem GroundTheory.LocalField.finiteExtensionStructure_vle_iff (x y : L) :
    letI := normedField K
    letI := spectralNormedField K L
    letI := (finiteExtensionStructure K L).rel
    x ≤ᵥ y ↔ ‖x‖ ≤ ‖y‖ := by sorry
