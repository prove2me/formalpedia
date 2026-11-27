-- Prove2me | Theorems.Thm_GroundTheory_LocalField_residueDegree_eq_one_of_ramificationIndex_eq_finrank
-- name    : GroundTheory.LocalField.residueDegree_eq_one_of_ramificationIndex_eq_finrank
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:05:18.403953+00:00
-- url     : https://prove2.me/theorems/5a9dae83-a09c-4861-835a-b0f82faf6339
-- title:
--   Local Field: residue Degree eq one of ramification Index eq finrank
-- statement:
--   The Local Field construction uses the residue Degree eq one of ramification Index eq finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L188-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L188-L193

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
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.residueDegree_eq_one_of_ramificationIndex_eq_finrank
    (h : ramificationIndex K L = Module.finrank K L) : residueDegree K L = 1 := by sorry
