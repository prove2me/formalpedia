-- Prove2me | Theorems.Thm_GlobalTheory_exists_prime_finite_quotient_atPrime
-- name    : GlobalTheory.exists_prime_finite_quotient_atPrime
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:50:28.376816+00:00
-- url     : https://prove2.me/theorems/2e0cb8b0-ba98-5c30-8c78-ff1fc1b5cd4f
-- title:
--   Global Theory: exists prime finite quotient at Prime
-- statement:
--   The Global Theory construction uses the exists prime finite quotient at Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L64-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L64-L106

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

theorem GlobalTheory.exists_prime_finite_quotient_atPrime {R A : Type*} [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] [CommRing A] [IsNoetherianRing A] [Algebra R A]
    (m : Ideal A) [m.IsMaximal] [Finite (A ⧸ m)]
    (hm : (maximalIdeal R).map (algebraMap R A) ≤ m) {q : Ideal A} (hq : q.IsPrime) (hqm : q ≤ m)
    {ϖ : R} (hϖ : ϖ ∈ maximalIdeal R) {f : A} (hf : algebraMap R A ϖ * f ∉ q) :
    ∃ Q : Ideal (Localization.AtPrime m), Q.IsPrime ∧
      algebraMap A _ (algebraMap R A ϖ * f) ∉ Q ∧ Module.Finite R (Localization.AtPrime m ⧸ Q) := by sorry
