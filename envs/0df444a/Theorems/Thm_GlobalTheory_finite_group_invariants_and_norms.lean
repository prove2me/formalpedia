-- Prove2me | Theorems.Thm_GlobalTheory_finite_group_invariants_and_norms
-- name    : GlobalTheory.finite_group_invariants_and_norms
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:59.711465+00:00
-- url     : https://prove2.me/theorems/d09004f3-8a13-4af2-b350-c6463413aac4
-- title:
--   Global Theory: finite group invariants and norms
-- statement:
--   The Global Theory construction uses the finite group invariants and norms property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L901-L966
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUnitSmulEqOfBijectiveToSpanSingleton.lean#L901-L966

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
universe u v

theorem GlobalTheory.finite_group_invariants_and_norms (G : Type v) [Group G] [Finite G]
    (A : Type u) [CommRing A] [MulSemiringAction G A] :
    Algebra.IsIntegral (FixedPoints.subring A G) A ∧
    (IsDomain A → IsIntegrallyClosed A →
      IsDomain (FixedPoints.subring A G) ∧ IsIntegrallyClosed (FixedPoints.subring A G)) ∧
    (∀ (R : Type u) [CommRing R] [Algebra R A] [SMulCommClass G R A] [IsNoetherianRing R]
      [Algebra.FiniteType R A],
      Algebra.FiniteType R (FixedPoints.subalgebra R A G) ∧
        Module.Finite (FixedPoints.subalgebra R A G) A) ∧
    (∀ (P : Ideal (FixedPoints.subring A G)) [P.IsPrime],
      ∃ Q : Ideal A, Q.IsPrime ∧ Q.LiesOver P ∧ MulAction.orbit G Q = P.primesOver A) ∧
    (∀ (R S M : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
      [AddCommGroup M] [Module R M] (ρ : Representation R G M),
      Function.Injective (ρ.invariants.subtype.baseChange S) ∧
        ∀ x : S ⊗[R] M, x ∈ ρ.invariants.baseChange S ↔ ∀ g, (ρ g).baseChange S x = x) ∧
    (∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S] [Algebra R A]
      [SMulCommClass G R A],
      letI := tensorMulSemiringAction G R S A
      haveI := tensorMulSemiringAction_smulCommClass G R S A
      IsBaseChange S (fixedSubalgebraMap G S
        (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A)
        (tensorMulSemiringAction_includeRight G R S A)).toLinearMap) ∧
    (∀ T : Submonoid (FixedPoints.subring A G),
      letI := localizationMulSemiringAction G (Algebra.algebraMapSubmonoid A T)
        (smul_mem_algebraMapSubmonoid G T) (Localization (Algebra.algebraMapSubmonoid A T))
      Function.Injective
        (algebraMap (Localization T) (Localization (Algebra.algebraMapSubmonoid A T))) ∧
      ∀ x : Localization (Algebra.algebraMapSubmonoid A T),
        (∀ g : G, g • x = x) ↔ ∃ y : Localization T, algebraMap _ _ y = x) ∧
    (∀ (M : Type u) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
      (κ : Fin (Nat.card G) ≃ G) (e : M),
      Function.Bijective (LinearMap.toSpanSingleton A M e) →
      letI := piTensorDistribMulAction G A (fun _ : Fin (Nat.card G) ↦ M)
      Function.Bijective
        (LinearMap.toSpanSingleton A (⨂[A]^(Nat.card G) M) (tensorNorm A κ e)) ∧
      (∀ g : G, g • tensorNorm A κ e = tensorNorm A κ e) ∧
      (∀ e' : M, Function.Bijective (LinearMap.toSpanSingleton A M e') →
        ∃ u : (FixedPoints.subring A G)ˣ,
          tensorNorm A κ e' = ((u : FixedPoints.subring A G) : A) • tensorNorm A κ e) ∧
      ∀ y : ⨂[A]^(Nat.card G) M,
        (∀ g : G, g • y = y) ↔ ∃ a ∈ FixedPoints.subring A G, y = a • tensorNorm A κ e) ∧
    (∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Invertible A M],
      Finite (MaximalSpectrum A) →
        Module.Free A M ∧ ∃ e : M, Function.Bijective (LinearMap.toSpanSingleton A M e)) := by sorry
