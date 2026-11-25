-- Prove2me | Theorems.Thm_GlobalTheory_exists_model_ringOfIntegers
-- name    : GlobalTheory.exists_model_ringOfIntegers
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:35:04.410226+00:00
-- url     : https://prove2.me/theorems/1c3b5801-ce3c-4ace-8c00-6dfd645f11b7
-- title:
--   Global Theory: exists model ring Of Integers
-- statement:
--   The Global Theory construction uses the exists model ring Of Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDiscreteValuationRingValuationSubringAtPrime.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsDiscreteValuationRingValuationSubringAtPrime.lean#L34-L42

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
variable {M : Type*} [Field M] [CharZero M] {L : Type*} [Field L] [Algebra M L] [IsAlgClosed L]
  {W : WeierstrassCurve M} [W.IsElliptic]

theorem GlobalTheory.exists_model_ringOfIntegers (hj : IsIntegral ℤ W.j) (h : HasRationalTorsion W L 12)
    (M' : Type*) [Field M'] [Algebra M M'] :
    ∃ (C : VariableChange M') (W₀ : WeierstrassCurve (𝓞 M')),
      C • W.baseChange M' = W₀.baseChange M' ∧ W₀.Δ = 1 := by sorry
