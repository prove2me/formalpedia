-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_QuaternionExample_cocycle_eq_candidate
-- name    : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.cocycle_eq_candidate
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:52:18.438194+00:00
-- url     : https://prove2.me/theorems/2f46e99b-f062-4f17-8ff0-f286ed9ec31d
-- title:
--   Quaternion cocycles are determined by generator values
-- statement:
--   Let $Q_8=\{\pm1,\pm i,\pm j,\pm k\}$ be the quaternion group, and write $S_3=\langle r,s\mid r^3=s^2=1,\ srs=r^{-1}\rangle$. Use the action in which $r$ sends $(i,j,k)$ to $(j,k,i)$ and $s$ sends $(i,j,k)$ to $(-j,-i,-k)$.
--
--   Let $f:S_3\to Q_8$ be a cocycle, meaning $f(xy)=f(x)(x\cdot f(y))$. Put $a=f(r)$, $b=f(s)$, and $(a_0,a_1,a_2)=(1,a,a(r\cdot a))$. Then
--
--   $$
--   \forall m\in\{0,1,2\},\qquad f(r^m)=a_m,\qquad f(sr^m)=b(s\cdot a_m).
--   $$
--
--   This gives the explicit reconstruction formula used to classify cocycles in the quaternion example.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/Counterexamples/Quaternion.lean, lines 89–104; source SHA-256 ddcb8985f23e0c604c8d41f84b6ebe9f1b50c76827c48551414cc89e024c7cb4.

import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
import Definitions.Def_LocalConjugacy_Proof_ConcreteGroups
import Definitions.Def_LocalConjugacy_Targets
import Definitions.Def_LocalConjugacy_Proof_Compactness
import Definitions.Def_LocalConjugacy_Proof_ProfiniteSylow
import Definitions.Def_LocalConjugacy_Proof_StructuralImages
import Definitions.Def_LocalConjugacy_Proof_FiniteAbelianCohomology
import Definitions.Def_LocalConjugacy_Proof_AbelianComplement
import Definitions.Def_LocalConjugacy_Proof_QuotientReduction
import Definitions.Def_LocalConjugacy_Proof_Cohomology
import Definitions.Def_LocalConjugacy_Proof_InvariantRestriction
import Definitions.Def_LocalConjugacy_Proof_CocycleActions
import Definitions.Def_LocalConjugacy_Proof_CoprimeCohomology
import Definitions.Def_LocalConjugacy_Proof_CocycleDescent
import Definitions.Def_LocalConjugacy_Proof_CocycleZorn
import Definitions.Def_LocalConjugacy_Proof_CocycleProducts
import Definitions.Def_LocalConjugacy_Proof_FiniteCoefficientSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInvarianceSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInjectivity
import Definitions.Def_LocalConjugacy_Proof_CocycleRebase
import Definitions.Def_LocalConjugacy_Proof_FiniteHall
import Definitions.Def_LocalConjugacy_Proof_SupersolvableStructure
import Definitions.Def_LocalConjugacy_Proof_ProfiniteHall
import Definitions.Def_LocalConjugacy_Proof_ActionProductTopology
import Definitions.Def_LocalConjugacy_Proof_HallCohomology
import Definitions.Def_LocalConjugacy_Proof_SupersolvableRestriction
import Definitions.Def_LocalConjugacy_Proof_NilpotentCoefficients
import Definitions.Def_LocalConjugacy_Proof_NonabelianComplement
import Definitions.Def_LocalConjugacy_Proof_ComplementSupersolvable
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Quaternion
import Definitions.Def_LocalConjugacy_Proof_QuaternionCohomology
import Definitions.Def_LocalConjugacy_Proof_QuaternionMatrices
import Definitions.Def_LocalConjugacy_Proof_QuaternionAction
import Definitions.Def_LocalConjugacy_Proof_QuaternionComplements

theorem LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.cocycle_eq_candidate :
∀
  (f :
    LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S → LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q)
  (hf : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.IsCocycle f),
  @Eq.{1}
    (LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S → LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q)
    f
    (LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.candidate
      (f
        (@DihedralGroup.r (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 1)
            (@One.toOfNat1.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@AddMonoidWithOne.toOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@AddGroupWithOne.toAddMonoidWithOne.{0}
                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (@Field.toDivisionRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          Nat.fact_prime_three))))))))))
      (f
        (@DihedralGroup.sr (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 0)
            (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@instMulZeroClassOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (@Semifield.toDivisionSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                        (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          Nat.fact_prime_three))))))))))) := by sorry
