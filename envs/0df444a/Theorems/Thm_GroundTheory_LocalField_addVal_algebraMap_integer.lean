-- Prove2me | Theorems.Thm_GroundTheory_LocalField_addVal_algebraMap_integer
-- name    : GroundTheory.LocalField.addVal_algebraMap_integer
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:58:52.310439+00:00
-- url     : https://prove2.me/theorems/e152b317-ef43-45a2-9da2-e551e170f7ce
-- title:
--   Local Field: add Val algebra Map integer
-- statement:
--   The Local Field construction uses the add Val algebra Map integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L42-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L42-L57

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
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.addVal_algebraMap_integer (x : 𝒪[K]) :
    addVal 𝒪[L] (algebraMap 𝒪[K] 𝒪[L] x) = ramificationIndex K L * addVal 𝒪[K] x := by sorry
