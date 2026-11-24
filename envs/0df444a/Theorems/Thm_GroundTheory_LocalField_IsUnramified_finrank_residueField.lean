-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsUnramified_finrank_residueField
-- name    : GroundTheory.LocalField.IsUnramified.finrank_residueField
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:43:58.533327+00:00
-- url     : https://prove2.me/theorems/75c75484-7ce3-4878-a601-1abbfa2a1c83
-- title:
--   Is Unramified: finrank residue Field
-- statement:
--   The Is Unramified construction uses the finrank residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedDefs.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedDefs.lean#L53-L55

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

theorem GroundTheory.LocalField.IsUnramified.finrank_residueField [IsUnramified K L] :
    Module.finrank 𝓀[K] 𝓀[L] = Module.finrank K L := by sorry
