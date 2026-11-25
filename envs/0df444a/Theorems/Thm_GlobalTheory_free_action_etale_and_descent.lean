-- Prove2me | Theorems.Thm_GlobalTheory_free_action_etale_and_descent
-- name    : GlobalTheory.free_action_etale_and_descent
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:57.268852+00:00
-- url     : https://prove2.me/theorems/53103874-5e66-4876-afae-08688691af4b
-- title:
--   Global Theory: free action etale and descent
-- statement:
--   The Global Theory construction uses the free action etale and descent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L784-L826
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsFreeRingActionIffInertiaEqBotOfIsPrime.lean#L784-L826

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
universe w v u
open CategoryTheory

theorem GlobalTheory.free_action_etale_and_descent (G : Type v) [Group G] [Finite G]
    (A : Type u) [CommRing A] [MulSemiringAction G A] :
    (IsFreeRingAction G A →
      Module.Finite (FixedPoints.subring A G) A ∧ Algebra.Etale (FixedPoints.subring A G) A ∧
      Module.Projective (FixedPoints.subring A G) A ∧
      Module.FaithfullyFlat (FixedPoints.subring A G) A ∧
      (∀ p : PrimeSpectrum (FixedPoints.subring A G), Module.rankAtStalk A p = Nat.card G) ∧
      (∃ e : A ⊗[FixedPoints.subring A G] A ≃ₐ[A] (G → A),
        ∀ (a b : A) (g : G), e (a ⊗ₜ b) g = a * g • b) ∧
      (SemilinearModule.invariantsFunctor.{max w u} G A).IsEquivalence ∧
      (∀ (M : Type w) [AddCommGroup M] [Module A M] [DistribMulAction G M]
        [SMulDistribClass G A M],
        Function.Bijective ((Representation.ofDistribMulAction
          (FixedPoints.subring A G) G M).invariants.subtype.liftBaseChange A) ∧
        ((Module.Finite (FixedPoints.subring A G)
            (Representation.ofDistribMulAction (FixedPoints.subring A G) G M).invariants ∧
          Module.Projective (FixedPoints.subring A G)
            (Representation.ofDistribMulAction (FixedPoints.subring A G) G M).invariants) ↔
          (Module.Finite A M ∧ Module.Projective A M))) ∧
      ∀ (N : Type w) [AddCommGroup N] [Module (FixedPoints.subring A G) N],
        Function.Bijective (FreeQuotient.toInvariantsTensor G A (FixedPoints.subring A G) N)) ∧
    ∀ (M : Type w) [AddCommGroup M] [Module A M] [DistribMulAction G M]
      [SMulDistribClass G A M] [Module.Finite A M] [Module.Projective A M],
      (∀ P : Ideal A, P.IsMaximal → (Nat.card (P.inertia G) : A) ∉ P) →
      (∀ P : Ideal A, P.IsMaximal → ∀ g ∈ P.inertia G, ∀ m : M,
        g • m - m ∈ P • (⊤ : Submodule A M)) →
      Function.Bijective ((Representation.ofDistribMulAction
        (FixedPoints.subring A G) G M).invariants.subtype.liftBaseChange A) ∧
      Module.Finite (FixedPoints.subring A G)
        (Representation.ofDistribMulAction (FixedPoints.subring A G) G M).invariants ∧
      Module.Projective (FixedPoints.subring A G)
        (Representation.ofDistribMulAction (FixedPoints.subring A G) G M).invariants := by sorry
