-- Prove2me | Theorems.Thm_GlobalTheory_DvrModel_prime_element_and_extension
-- name    : GlobalTheory.DvrModel.prime_element_and_extension
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:04:39.947981+00:00
-- url     : https://prove2.me/theorems/7d3e7218-5fed-4373-9a51-23a61b65eabc
-- title:
--   Dvr Model: prime element and extension
-- statement:
--   The Dvr Model construction uses the prime element and extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean#L402-L453
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsDiscreteValuationRingStalkGeneric.lean#L402-L453

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.DvrModel

theorem GlobalTheory.DvrModel.prime_element_and_extension :
    (∀ (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (π : R)
      [(Ideal.span {π}).IsPrime], π ≠ 0 →
      ∀ (A : Type u) [CommRing A] [Algebra R A] [IsLocalization.Away π A]
        (S : Type u) [CommRing S] [Algebra R S] [IsLocalization.AtPrime S (Ideal.span {π})]
        (F : Type u) [Field F] [Algebra R F] [IsFractionRing R F]
        [Algebra A F] [IsScalarTower R A F] [Algebra S F] [IsScalarTower R S F],
      ∃ (_ : IsDomain S) (_ : IsDiscreteValuationRing S) (_ : IsFractionRing S F),
        Irreducible (algebraMap R S π) ∧
        (algebraMap A F).range ⊓ (algebraMap S F).range = (algebraMap R F).range ∧
        (∀ y : A, IsUnit y →
          (IsDiscreteValuationRing.maximalIdeal S).valuation F (algebraMap A F y) = 1 →
          ∃ r : R, IsUnit r ∧ algebraMap R A r = y) ∧
        ∀ x : R, (∀ n : ℕ, π ^ n ∣ x) → x = 0) ∧
    ∀ (V : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      (K : Type u) [Field K] [Algebra V K] [IsFractionRing V K] (ϖ : V), Irreducible ϖ →
      ∀ (H HK Hs : Scheme.{u}) (f : H ⟶ Spec (.of V)) [Flat f] [LocallyOfFiniteType f]
        (j : HK ⟶ H) (fK : HK ⟶ Spec (.of K)) [IsIntegral HK]
        (i : Hs ⟶ H) (fs : Hs ⟶ Spec (.of (ResidueField V))) [IsIntegral Hs],
      IsPullback j fK f (Spec.map (CommRingCat.ofHom (algebraMap V K))) →
      IsPullback i fs f (Spec.map (CommRingCat.ofHom (residue V))) →
      ∀ L : LB H, L.IsLB →
      (∀ (e : Spec (.of V) ⟶ H) (eK : Spec (.of K) ⟶ HK), e ≫ f = 𝟙 _ →
        eK ≫ j = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ e →
        ∀ (r : LB.Gen (L.pull j)) (ρ : LB.Gen (L.pull e)), r.IsGen →
        LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ r eK)
          (LB.pullGen L _ _ ρ (Spec.map (CommRingCat.ofHom (algebraMap V K)))) →
        ∃! r' : LB.Gen L, r'.IsGen ∧ LB.genPull L r' j = r) ∧
      (∀ s : L.Sec, (∀ a (n : ℕ), (pullback.fst f (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (Ideal.span {ϖ ^ n}))))).app (L.U a) (s.f a) = 0) →
        ∀ a, s.f a = 0) ∧
      ∀ r : (L.pull j).Sec, (∃ a, r.f a ≠ 0) →
        ∃! n : ℤ, ∃ s : L.Sec,
          (∀ a : PUnit → L.ι,
            j.appLE (L.U (a ⟨⟩)) ((L.pull j).U a) (pull_U L j a).le (s.f (a ⟨⟩)) =
              HK.presheaf.map (homOfLE le_top).op
                (fK.appTop ((Scheme.ΓSpecIso (.of K)).inv (algebraMap V K ϖ ^ n))) * r.f a) ∧
          ∃ a, ∃ x, f x = closedPoint V ∧ x ∈ H.basicOpen (s.f a) := by sorry
