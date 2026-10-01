-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_prosupersolvable_hall_split_containing
-- name    : LocalConjugacy.Proof.LocalConjugacy.prosupersolvable_hall_split_containing
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:11:53.57016+00:00
-- url     : https://prove2.me/theorems/d7a80ed9-f3e7-4e8a-8cfd-19f28ee7b6a4
-- title:
--   A profinite Hall splitting containing a chosen Sylow subgroup
-- statement:
--   Let $G$ be a prosupersolvable profinite group, $n\in\mathbb N$, and $p\le n$ a prime. Let $P\le G$ be a Sylow pro-$p$ subgroup. Then there are closed subgroups $M,Q\le G$ such that
--
--   $$
--   M\trianglelefteq G,\qquad G=MQ,\qquad M\cap Q=1,\qquad P\le Q,
--   $$
--
--   where $M$ is a Hall pro-subgroup for primes greater than $n$, and $Q$ is a Hall pro-subgroup for primes at most $n$. A Hall pro-subgroup means a closed subgroup whose image is a Hall subgroup for the specified prime set in every finite continuous quotient.
--
--   This gives the profinite Hall cutoff decomposition while retaining a prescribed Sylow subgroup in the complementary factor.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/ProfiniteHall.lean, lines 214–263; source SHA-256 5bc8b50236c68c4f09b947c789183f5f2267a1734ba468b979d7ad6168ba9c97.

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

universe u_1

theorem LocalConjugacy.Proof.LocalConjugacy.prosupersolvable_hall_split_containing :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1]
  (hG : @LocalConjugacy.Proof.LocalConjugacy.Prosupersolvable.{u_1} G inst inst_1) {n p : Nat} [Fact (Nat.Prime p)]
  (hpn : @LE.le.{0} Nat instLENat p n) (P : @Subgroup.{u_1} G inst)
  (hP :
    @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1} p G inst inst_1
      (@Top.top.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instTop.{u_1} G inst)) P),
  @Exists.{u_1 + 1} (@Subgroup.{u_1} G inst) fun (M : @Subgroup.{u_1} G inst) =>
    @Exists.{u_1 + 1} (@Subgroup.{u_1} G inst) fun (Q : @Subgroup.{u_1} G inst) =>
      And (@Subgroup.Normal.{u_1} G inst M)
        (And
          (@LocalConjugacy.Proof.LocalConjugacy.IsHallPro.{u_1} G inst inst_1
            (@Set.ofPred.{0} Nat fun (r : Nat) => @LT.lt.{0} Nat instLTNat n r) M)
          (And
            (@LocalConjugacy.Proof.LocalConjugacy.IsHallPro.{u_1} G inst inst_1
              (@Set.ofPred.{0} Nat fun (r : Nat) => @LE.le.{0} Nat instLENat r n) Q)
            (And (@Subgroup.IsComplement'.{u_1} G inst M Q)
              (@LE.le.{u_1} (@Subgroup.{u_1} G inst)
                (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
                  (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
                P Q)))) := by sorry
