-- Prove2me | Theorems.Thm_GlobalTheory_exists_prime_natCast_mem_of_finiteType_int
-- name    : GlobalTheory.exists_prime_natCast_mem_of_finiteType_int
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:51:10.085895+00:00
-- url     : https://prove2.me/theorems/9e15431d-b942-43fd-97d1-b7e520b0373a
-- title:
--   Global Theory: exists prime nat Cast mem of finite Type int
-- statement:
--   The Global Theory construction uses the exists prime nat Cast mem of finite Type int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L283-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L283-L290

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

theorem GlobalTheory.exists_prime_natCast_mem_of_finiteType_int {A : Type*} [CommRing A]
    [Algebra.FiniteType ℤ A] (m : Ideal A) [m.IsMaximal] : ∃ p : ℕ, p.Prime ∧ (p : A) ∈ m := by sorry
