-- Prove2me | Theorems.Thm_GroundTheory_LocalField_principalFiltration_antitone
-- name    : GroundTheory.LocalField.principalFiltration_antitone
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:01:00.83818+00:00
-- url     : https://prove2.me/theorems/ebfcec74-1a3a-508e-b9e8-d2ed44e8ba10
-- title:
--   Local Field: principal Filtration antitone
-- statement:
--   The Local Field construction uses the principal Filtration antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsModule.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/PrincipalUnitsModule.lean#L26-L29

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicExp
import Definitions.Def_GroundTheory_LocalFields_PrincipalUnitsModule
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
open ValuativeRel IsLocalRing Topology Filter
open scoped WithZero
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.principalFiltration_antitone : Antitone (principalFiltration K) := by sorry
