-- Prove2me | Theorems.Thm_GroundTheory_LocalField_Padic_stdCharOf_apply
-- name    : GroundTheory.LocalField.Padic.stdCharOf_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:06:44.716479+00:00
-- url     : https://prove2.me/theorems/ed75092b-e1f6-5baa-9bf6-18f1f61d6d2e
-- title:
--   Padic: std Char Of apply
-- statement:
--   The Padic construction uses the std Char Of apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L233-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierPadic.lean#L233-L233

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
omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeExtension ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

theorem GroundTheory.LocalField.Padic.stdCharOf_apply (x : K) : stdCharOf p K x = stdChar p (Algebra.trace ℚ_[p] K x) := by sorry
