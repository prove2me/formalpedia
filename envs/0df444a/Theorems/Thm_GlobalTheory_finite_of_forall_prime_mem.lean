-- Prove2me | Theorems.Thm_GlobalTheory_finite_of_forall_prime_mem
-- name    : GlobalTheory.finite_of_forall_prime_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:50:50.319178+00:00
-- url     : https://prove2.me/theorems/f6c9f746-59bc-5f09-b8f3-c2b02d28d85b
-- title:
--   Global Theory: finite of forall prime mem
-- statement:
--   The Global Theory construction uses the finite of forall prime mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L22-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L22-L43

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

theorem GlobalTheory.finite_of_forall_prime_mem {R B : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [IsLocalRing B] [Algebra R B] [Finite (B ⧸ maximalIdeal B)] {f : B} (hf : f ≠ 0)
    (H : ∀ P : Ideal B, P.IsPrime → P ≠ ⊥ → f ∈ P)
    (h0 : (maximalIdeal R).map (algebraMap R B) ≠ ⊥)
    (h1 : (maximalIdeal R).map (algebraMap R B) ≠ ⊤) : Module.Finite R B := by sorry
