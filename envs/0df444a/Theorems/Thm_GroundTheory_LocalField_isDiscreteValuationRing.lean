-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isDiscreteValuationRing
-- name    : GroundTheory.LocalField.isDiscreteValuationRing
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:59:52.697195+00:00
-- url     : https://prove2.me/theorems/6c5d7295-6c2c-4655-89ba-f6eea469f3b7
-- title:
--   Local Field: is Discrete Valuation Ring
-- statement:
--   The Local Field construction uses the is Discrete Valuation Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Integers.lean#L107-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Integers.lean#L107-L107

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

theorem GroundTheory.LocalField.isDiscreteValuationRing : IsDiscreteValuationRing 𝒪[L] := by sorry
