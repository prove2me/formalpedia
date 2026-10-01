-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_fixed_cocycle_trivial_on_intersection
-- name    : LocalConjugacy.Proof.LocalConjugacy.fixed_cocycle_trivial_on_intersection
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:54:42.734206+00:00
-- url     : https://prove2.me/theorems/ecdcfb81-f032-4ff2-888c-48f2c6efde89
-- title:
--   A fixed cocycle vanishes on a coprime intersection
-- statement:
--   Let $J$ be a profinite group acting continuously by automorphisms on a discrete group $N$. Let $p,q\in\mathbb N$ be coprime, and assume that every element of $N$ is killed by some power of $p$. Let $K\trianglelefteq J$ and $Q\le J$, where $Q$ is procyclic and every quotient of $Q$ by an open normal subgroup has each element killed by a power of $q$. Let $g:K\to N$ be a continuous cocycle fixed under twisting by $Q$: for all $a\in Q$ and $x\in K$, $a\cdot g(a^{-1}xa)=g(x)$. Then
--
--   $$\forall x\in Q\cap K,\qquad g(x)=1.$$
--
--   This identifies the intersection on which a fixed cocycle is trivial, allowing cocycle constructions across a procyclic supplement.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/FixedCocycle.lean, lines 38–66; source SHA-256 1e9a9a5984ac4cfd32a19746c1f84ca2a00f7ce41edded55cce574fd4f0c31dc.

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

theorem LocalConjugacy.Proof.LocalConjugacy.fixed_cocycle_trivial_on_intersection :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [inst_3 : @LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@IsTopologicalGroup.{u_2} N inst_4 inst_1] [@DiscreteTopology.{u_2} N inst_4]
  [inst_7 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [inst_8 :
    @ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_7)))
      inst_2 inst_4]
  {p q : Nat} (hpq : Nat.Coprime p q) (hN : @IsPGroup.{u_2} p N inst_1) (K Q : @Subgroup.{u_1} J inst)
  [inst_9 : @Subgroup.Normal.{u_1} J inst K]
  (hcyclic :
    @LocalConjugacy.Proof.LocalConjugacy.Procyclic.{u_1}
      (@Subtype.{u_1 + 1} J fun (x : J) =>
        @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
      (@Subgroup.toGroup.{u_1} J inst Q)
      (@instTopologicalSpaceSubtype.{u_1} J
        (fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
        inst_2))
  (hQ :
    @LocalConjugacy.Proof.LocalConjugacy.IsProP.{u_1} q
      (@Subtype.{u_1 + 1} J fun (x : J) =>
        @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
      (@Subgroup.toGroup.{u_1} J inst Q)
      (@instTopologicalSpaceSubtype.{u_1} J
        (fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
        inst_2))
  (g : @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 K)
  (hfix :
    ∀
      (x :
        @Subtype.{u_1 + 1} J fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x),
      @Eq.{max (u_1 + 1) (u_2 + 1)}
        (@LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 K)
        (@LocalConjugacy.Proof.LocalConjugacy.twistCocycle.{u_1, u_2} J N inst inst_1 inst_2
          (@LocalConjugacy.Proof.LocalConjugacy.Profinite.toIsTopologicalGroup.{u_1} J inst inst_2 inst_3) inst_4 inst_7
          inst_8 K inst_9 g
          (@Subtype.val.{u_1 + 1} J
            (fun (x : J) =>
              @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q
                x)
            x))
        g)
  (x : J),
  @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x →
    ∀
      (hx :
        @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) K x),
      @Eq.{u_2 + 1} N
        (@LocalConjugacy.Cocycle.toFun.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 K g
          (@Subtype.mk.{u_1 + 1} J
            (fun (x : J) =>
              @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) K
                x)
            x hx))
        (@OfNat.ofNat.{u_2} N (nat_lit 1)
          (@One.toOfNat1.{u_2} N
            (@InvOneClass.toOne.{u_2} N
              (@DivInvOneMonoid.toInvOneClass.{u_2} N
                (@DivisionMonoid.toDivInvOneMonoid.{u_2} N (@Group.toDivisionMonoid.{u_2} N inst_1)))))) := by sorry
