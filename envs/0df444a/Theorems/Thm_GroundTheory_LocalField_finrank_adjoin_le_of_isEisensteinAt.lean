-- Prove2me | Theorems.Thm_GroundTheory_LocalField_finrank_adjoin_le_of_isEisensteinAt
-- name    : GroundTheory.LocalField.finrank_adjoin_le_of_isEisensteinAt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:14:23.285976+00:00
-- url     : https://prove2.me/theorems/e865b12d-dc56-43d4-91b9-5f826863723c
-- title:
--   Local Field: finrank adjoin le of is Eisenstein At
-- statement:
--   The Local Field construction uses the finrank adjoin le of is Eisenstein At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L242-L252
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L242-L252

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_Eisenstein
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
open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped _root_.IntermediateField
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable [Field L] [Algebra K L]

theorem GroundTheory.LocalField.finrank_adjoin_le_of_isEisensteinAt {f : 𝒪[K][X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K])) {α : L} (hα : aeval α f = 0) :
    Module.finrank K K⟮α⟯ ≤ f.natDegree := by sorry
