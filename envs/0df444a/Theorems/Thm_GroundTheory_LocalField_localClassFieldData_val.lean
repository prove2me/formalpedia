-- Prove2me | Theorems.Thm_GroundTheory_LocalField_localClassFieldData_val
-- name    : GroundTheory.LocalField.localClassFieldData_val
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:07:06.760726+00:00
-- url     : https://prove2.me/theorems/45738df5-80e9-548d-8c1b-4e7fde98bfa6
-- title:
--   Local Field: local Class Field Data val
-- statement:
--   The Local Field construction uses the local Class Field Data val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiom.lean#L115-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalAxiom.lean#L115-L116

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomDictionary
import Definitions.Def_GroundTheory_LocalFields_HerbrandLocal
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalAxiom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Abstract ValuativeRel
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
variable {K Ω}
variable (K Ω)

theorem GroundTheory.LocalField.localClassFieldData_val : (localClassFieldData K Ω).val = localValuation K Ω := by sorry

attribute [defeq] GroundTheory.LocalField.localClassFieldData_val
