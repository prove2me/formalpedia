-- Prove2me | Theorems.Thm_GroundTheory_LocalField_forall_integer_mul_eq_one_iff
-- name    : GroundTheory.LocalField.forall_integer_mul_eq_one_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T09:23:53.828557+00:00
-- url     : https://prove2.me/theorems/3dcec0e1-8708-428e-85cc-32ac00e463b0
-- title:
--   Local Field: forall integer mul eq one iff
-- statement:
--   The Local Field construction uses the forall integer mul eq one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierTrace.lean#L97-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/LocalFourierTrace.lean#L97-L111

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
omit [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.forall_integer_mul_eq_one_iff (t : K) :
    (∀ a ∈ 𝒪[K], ψ (a * t) = 1) ↔ t ∈ valBall K (addCharConductor ψ) := by sorry
