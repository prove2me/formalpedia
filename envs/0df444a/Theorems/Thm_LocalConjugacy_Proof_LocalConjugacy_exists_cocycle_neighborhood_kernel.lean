-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_exists_cocycle_neighborhood_kernel
-- name    : LocalConjugacy.Proof.LocalConjugacy.exists_cocycle_neighborhood_kernel
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:03:55.35569+00:00
-- url     : https://prove2.me/theorems/499fe1bb-66c2-4199-9977-9dbc83143093
-- title:
--   An open normal subgroup kills a cocycle and fixes its image
-- statement:
--   Let $J$ be a profinite group acting continuously by automorphisms on a discrete group $N$. Let $H\le J$ be closed and $f:H\to N$ a continuous cocycle. Then there is an open normal subgroup $U\trianglelefteq J$ such that
--
--   $$
--   \forall u\in U\ \forall x\in H,\quad u\cdot f(x)=f(x),\qquad
--   \forall x\in H\cap U,\quad f(x)=1.
--   $$
--
--   This provides an open normal neighborhood simultaneously compatible with the cocycle and the action on its image, without assuming $N$ finite.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/CocycleNeighborhood.lean, lines 16–44; source SHA-256 d708cc0d5984b02fa63014c3330a19c97523def77ef9336dec26550725e897b0.

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

theorem LocalConjugacy.Proof.LocalConjugacy.exists_cocycle_neighborhood_kernel :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@DiscreteTopology.{u_2} N inst_4]
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
  (H : @Subgroup.{u_1} J inst)
  (hH :
    @IsClosed.{u_1} J inst_2
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) H))
  (f : @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 H),
  @Exists.{u_1 + 1} (@OpenNormalSubgroup.{u_1} J inst inst_2) fun (U : @OpenNormalSubgroup.{u_1} J inst inst_2) =>
    And
      (∀ (u : J),
        @Membership.mem.{u_1, u_1} J (@OpenNormalSubgroup.{u_1} J inst inst_2)
            (@SetLike.instMembership.{u_1, u_1} (@OpenNormalSubgroup.{u_1} J inst inst_2) J
              (@OpenNormalSubgroup.instSetLike.{u_1} J inst inst_2))
            U u →
          ∀
            (x :
              @Subtype.{u_1 + 1} J fun (x : J) =>
                @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) H
                  x),
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
                u (@LocalConjugacy.Cocycle.toFun.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 H f x))
              (@LocalConjugacy.Cocycle.toFun.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 H f x))
      (∀
        (x :
          @Subtype.{u_1 + 1} J fun (x : J) =>
            @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) H x),
        @Membership.mem.{u_1, u_1} J (@OpenNormalSubgroup.{u_1} J inst inst_2)
            (@SetLike.instMembership.{u_1, u_1} (@OpenNormalSubgroup.{u_1} J inst inst_2) J
              (@OpenNormalSubgroup.instSetLike.{u_1} J inst inst_2))
            U
            (@Subtype.val.{u_1 + 1} J
              (fun (x : J) =>
                @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) H
                  x)
              x) →
          @Eq.{u_2 + 1} N (@LocalConjugacy.Cocycle.toFun.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 H f x)
            (@OfNat.ofNat.{u_2} N (nat_lit 1)
              (@One.toOfNat1.{u_2} N
                (@InvOneClass.toOne.{u_2} N
                  (@DivInvOneMonoid.toInvOneClass.{u_2} N
                    (@DivisionMonoid.toDivInvOneMonoid.{u_2} N (@Group.toDivisionMonoid.{u_2} N inst_1))))))) := by sorry
