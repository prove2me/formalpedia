-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Padic_addCharConductor_stdCharOf
-- name    : GroundTheory.LocalField.Padic.addCharConductor_stdCharOf
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T09:35:08.668793+00:00
-- url     : https://prove2.me/theorems/1ab9066d-868f-504b-8af9-8393bca2a4d5
-- title:
--   Padic: add Char Conductor std Char Of
-- statement:
--   The Padic construction uses the add Char Conductor std Char Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L241-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L241-L244

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierTrace
import Definitions.Def_GroundTheory_LocalFields_LocalFourierPadic
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
open ValuativeRel MeasureTheory
open scoped NNReal ENNReal
open GroundTheory.LocalField.Padic
variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Algebra ℚ_[p] K] [ValuativeExtension ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

theorem GroundTheory.LocalField.Padic.addCharConductor_stdCharOf :
    addCharConductor (stdCharOf p K) = -(differentExponent ℚ_[p] K : ℤ) := by sorry
