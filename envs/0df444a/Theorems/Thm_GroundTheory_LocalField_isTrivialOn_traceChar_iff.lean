-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isTrivialOn_traceChar_iff
-- name    : GroundTheory.LocalField.isTrivialOn_traceChar_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T09:21:50.228441+00:00
-- url     : https://prove2.me/theorems/80711dfa-27ac-52b0-8af3-a97b1d93695d
-- title:
--   Local Field: is Trivial On trace Char iff
-- statement:
--   The Local Field construction uses the is Trivial On trace Char iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierTrace.lean#L115-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierTrace.lean#L115-L175

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Different
import Definitions.Def_GroundTheory_LocalFields_LocalFourierExistence
import Definitions.Def_GroundTheory_LocalFields_LocalFourierTrace
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
open scoped nonZeroDivisors
attribute [local instance high] FaithfulSMul.to_isTorsionFree
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable [ValuativeRel K] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [ValuativeExtension K L]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [FiniteDimensional K L]
variable {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1
variable [Algebra.IsSeparable K L]

theorem GroundTheory.LocalField.isTrivialOn_traceChar_iff (m : ℤ) :
    IsTrivialOn (traceChar L ψ) m ↔
      (ramificationIndex K L : ℤ) * addCharConductor ψ - differentExponent K L ≤ m := by sorry
