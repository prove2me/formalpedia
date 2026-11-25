-- Prove2me | Theorems.Thm_GlobalTheory_mem_integralClosure_padicInt_iff
-- name    : GlobalTheory.mem_integralClosure_padicInt_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:50:50.274378+00:00
-- url     : https://prove2.me/theorems/8891b73c-383f-43dc-a512-d42cb10f7c24
-- title:
--   Global Theory: mem integral Closure padic Int iff
-- statement:
--   The Global Theory construction uses the mem integral Closure padic Int iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L182-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L182-L185

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PrimeEqBotOrMaximalIdealOfIsFieldAway
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing TensorProduct
variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [Algebra ℚ_[p] K] [Algebra ℤ_[p] K]
  [IsScalarTower ℤ_[p] ℚ_[p] K] [FiniteDimensional ℚ_[p] K]
variable {p K}
variable {L : Type*} [Field L] [Algebra ℚ_[p] L] [Algebra ℤ_[p] L]
  [IsScalarTower ℤ_[p] ℚ_[p] L] [FiniteDimensional ℚ_[p] L]

theorem GlobalTheory.mem_integralClosure_padicInt_iff (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (x : K) :
    x ∈ integralClosure ℤ_[p] K ↔ ‖(x : PadicAlgCl p)‖ ≤ 1 := by sorry
