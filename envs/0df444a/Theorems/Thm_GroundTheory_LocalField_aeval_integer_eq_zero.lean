-- Prove2me | Theorems.Thm_GroundTheory_LocalField_aeval_integer_eq_zero
-- name    : GroundTheory.LocalField.aeval_integer_eq_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:59:15.427599+00:00
-- url     : https://prove2.me/theorems/d1478f82-f1ca-497b-b428-5a5662b7999c
-- title:
--   Local Field: aeval integer eq zero
-- statement:
--   The Local Field construction uses the aeval integer eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L284-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Eisenstein.lean#L284-L290

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
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  {f : 𝒪[K][X]}

theorem GroundTheory.LocalField.aeval_integer_eq_zero {α : L} (h : α ∈ 𝒪[L]) (hα : aeval α f = 0) :
    aeval (⟨α, h⟩ : 𝒪[L]) f = 0 := by sorry
