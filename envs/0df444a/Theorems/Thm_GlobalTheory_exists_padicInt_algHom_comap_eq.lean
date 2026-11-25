-- Prove2me | Theorems.Thm_GlobalTheory_exists_padicInt_algHom_comap_eq
-- name    : GlobalTheory.exists_padicInt_algHom_comap_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:51:19.239824+00:00
-- url     : https://prove2.me/theorems/b929a596-78a7-4c4e-8bd7-6d07b842fcde
-- title:
--   Global Theory: exists padic Int alg Hom comap eq
-- statement:
--   The Global Theory construction uses the exists padic Int alg Hom comap eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L294-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingIntegralClosurePadicInt.lean#L294-L324

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
variable {p : ℕ} [Fact p.Prime]

theorem GlobalTheory.exists_padicInt_algHom_comap_eq {A : Type*} [CommRing A] [IsNoetherianRing A]
    [Algebra ℤ_[p] A] (m : Ideal A) [m.IsMaximal] [Finite (A ⧸ m)] (hp : (p : A) ∈ m)
    {q : Ideal A} (hq : q.IsPrime) (hqm : q ≤ m) {f : A} (hf : (p : A) * f ∉ q) :
    ∃ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (_ : FiniteDimensional ℚ_[p] K)
      (y : A →ₐ[ℤ_[p]] integralClosure ℤ_[p] K),
      (maximalIdeal (integralClosure ℤ_[p] K)).comap y = m ∧ y f ≠ 0 := by sorry
