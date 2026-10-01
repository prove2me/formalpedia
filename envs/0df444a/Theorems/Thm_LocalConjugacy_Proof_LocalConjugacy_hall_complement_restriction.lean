-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_hall_complement_restriction
-- name    : LocalConjugacy.Proof.LocalConjugacy.hall_complement_restriction
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:11:19.184623+00:00
-- url     : https://prove2.me/theorems/a9c651a6-4d71-4338-a7dc-8bbca7ace09d
-- title:
--   Restriction across a trivially acting Hall factor
-- statement:
--   Let $J$ be a profinite group acting continuously by automorphisms on a discrete $p$-group $N$, where $p$ is prime. Let $M\trianglelefteq J$ and $Q\le J$ be closed complementary subgroups, so $J=MQ$ and $M\cap Q=\{1\}$. Assume that every finite continuous quotient of $M$ has order divisible only by primes greater than $p$, and that $M$ acts trivially on $N$. Then restriction of continuous nonabelian cocycles is injective on cohomology classes and is surjective onto the $J$-stable classes:
--
--   $$\operatorname{res}:H^1(J,N)\xrightarrow{\ \sim\ }H^1(Q,N)^{J\text{-stable}}.$$
--
--   Cohomologous cocycles differ by $g(x)=n^{-1}f(x)(x\cdot n)$ with a single $n\in N$. Stability means that $x\mapsto j\cdot f(j^{-1}xj)$ is cohomologous to $f$ on $Q\cap jQj^{-1}$ for every $j\in J$. This removes a complementary normal factor from the cohomology restriction problem.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/HallCohomology.lean, lines 159–197; source SHA-256 1d0d103e9a2c5244bd52aed3275317c01a49cfbe4a4703658b6cab294aa0e8bf.

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

universe u_1 u_2

theorem LocalConjugacy.Proof.LocalConjugacy.hall_complement_restriction :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@IsTopologicalGroup.{u_2} N inst_4 inst_1]
  [inst_6 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [@ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_6)))
      inst_2 inst_4]
  [@DiscreteTopology.{u_2} N inst_4] {p : Nat} [Fact (Nat.Prime p)] (hN : @IsPGroup.{u_2} p N inst_1)
  (M Q : @Subgroup.{u_1} J inst) [@Subgroup.Normal.{u_1} J inst M]
  (hM :
    @IsClosed.{u_1} J inst_2
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) M))
  (hQ :
    @IsClosed.{u_1} J inst_2
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) Q))
  (hs : @Subgroup.IsComplement'.{u_1} J inst M Q)
  (hprimes :
    @LocalConjugacy.Proof.LocalConjugacy.HasProPrimes.{u_1}
      (@Set.ofPred.{0} Nat fun (r : Nat) => @LT.lt.{0} Nat instLTNat p r)
      (@Subtype.{u_1 + 1} J fun (x : J) =>
        @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) M x)
      (@Subgroup.toGroup.{u_1} J inst M)
      (@instTopologicalSpaceSubtype.{u_1} J
        (fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) M x)
        inst_2))
  (hact :
    ∀
      (m :
        @Subtype.{u_1 + 1} J fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) M x)
      (n : N),
      @Eq.{u_2 + 1} N
        (@HSMul.hSMul.{u_1, u_2, u_2} J N N
          (@instHSMul.{u_1, u_2} J N
            (@SemigroupAction.toSMul.{u_1, u_2} J N
              (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
              (@MulAction.toSemigroupAction.{u_1, u_2} J N
                (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
                  (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_6))))
          (@Subtype.val.{u_1 + 1} J
            (fun (x : J) =>
              @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) M
                x)
            m)
          n)
        n),
  @LocalConjugacy.Proof.LocalConjugacy.RestrictionIsomorphism.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6
    (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) Q
    (@le_top.{u_1} (@Subgroup.{u_1} J inst)
      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
      (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
        (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
          (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
        (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instCompleteLattice.{u_1} J inst)))
      Q) := by sorry
