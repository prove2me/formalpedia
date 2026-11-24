-- Prove2me | Theorems.Thm_GlobalTheory_exists_finite_model_ringOfIntegers
-- name    : GlobalTheory.exists_finite_model_ringOfIntegers
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:31:47.234882+00:00
-- url     : https://prove2.me/theorems/ecd2101f-7f2b-48cc-a90f-39fe7981223a
-- title:
--   Global Theory: exists finite model ring Of Integers
-- statement:
--   The Global Theory construction uses the exists finite model ring Of Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDiscreteValuationRingValuationSubringAtPrime.lean#L117-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDiscreteValuationRingValuationSubringAtPrime.lean#L117-L129

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIntegralModelOfForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDiscreteValuationRingValuationSubringAtPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open WeierstrassCurve WeierstrassCurve.Affine Polynomial NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem GlobalTheory.exists_finite_model_ringOfIntegers {K : Type*} [Field K] [NumberField K]
    (W : WeierstrassCurve K) [W.IsElliptic] (hj : IsIntegral ℤ W.j) :
    ∃ M : IntermediateField K (AlgebraicClosure K), NumberField M ∧
      HasRationalTorsion (W.baseChange M) (AlgebraicClosure K) 12 ∧
      ∃ (C : VariableChange M) (W₀ : WeierstrassCurve (𝓞 M)),
        C • W.baseChange M = W₀.baseChange M ∧ W₀.Δ = 1 := by sorry
