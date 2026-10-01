-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_extend_fixed_cocycle
-- name    : LocalConjugacy.Proof.LocalConjugacy.extend_fixed_cocycle
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:53:49.730262+00:00
-- url     : https://prove2.me/theorems/9d445c3f-3af6-4cf0-b7f7-ff1dc2dddfd5
-- title:
--   Extension of a fixed cocycle across a supplement
-- statement:
--   Let $J$ be a profinite group acting continuously by automorphisms on a topological group $N$. Let $K\trianglelefteq J$ and $Q\le J$ be closed, with $J=KQ$. Let $f:K\to N$ be a continuous cocycle. Suppose $q\cdot f(q^{-1}xq)=f(x)$ for all $q\in Q$, $x\in K$, and $f(x)=1$ for every $x\in K\cap Q$. Then
--
--   $$
--   \exists F\in Z^1_{\mathrm{cts}}(J,N),\qquad F|_K=f,
--   $$
--
--   where $Z^1_{\mathrm{cts}}$ denotes continuous nonabelian cocycles.
--
--   This gives a cocycle-extension criterion in terms of fixedness under a supplement and compatibility on the intersection.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/CocycleExtension.lean, lines 16–83; source SHA-256 4d564abbcfef544ebdc09fcd63c06afedfb5c9730f1bf082b48415e0b2ad1b60.

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

theorem LocalConjugacy.Proof.LocalConjugacy.extend_fixed_cocycle :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [inst_3 : @LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@IsTopologicalGroup.{u_2} N inst_4 inst_1]
  [inst_6 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [inst_7 :
    @ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_6)))
      inst_2 inst_4]
  (K Q : @Subgroup.{u_1} J inst) [inst_8 : @Subgroup.Normal.{u_1} J inst K]
  (hK :
    @IsClosed.{u_1} J inst_2
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) K))
  (hQ :
    @IsClosed.{u_1} J inst_2
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) Q))
  (hs : @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} J inst K Q)
  (f : @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 K)
  (hfix :
    ∀
      (q :
        @Subtype.{u_1 + 1} J fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x),
      @Eq.{max (u_1 + 1) (u_2 + 1)}
        (@LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 K)
        (@LocalConjugacy.Proof.LocalConjugacy.twistCocycle.{u_1, u_2} J N inst inst_1 inst_2
          (@LocalConjugacy.Proof.LocalConjugacy.Profinite.toIsTopologicalGroup.{u_1} J inst inst_2 inst_3) inst_4 inst_6
          inst_7 K inst_8 f
          (@Subtype.val.{u_1 + 1} J
            (fun (x : J) =>
              @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q
                x)
            q))
        f)
  (htriv :
    ∀ (x : J),
      @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x →
        ∀
          (hx :
            @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) K x),
          @Eq.{u_2 + 1} N
            (@LocalConjugacy.Cocycle.toFun.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 K f
              (@Subtype.mk.{u_1 + 1} J
                (fun (x : J) =>
                  @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst))
                    K x)
                x hx))
            (@OfNat.ofNat.{u_2} N (nat_lit 1)
              (@One.toOfNat1.{u_2} N
                (@InvOneClass.toOne.{u_2} N
                  (@DivInvOneMonoid.toInvOneClass.{u_2} N
                    (@DivisionMonoid.toDivInvOneMonoid.{u_2} N (@Group.toDivisionMonoid.{u_2} N inst_1))))))),
  @Exists.{max (u_1 + 1) (u_2 + 1)}
    (@LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)))
    fun
      (F :
        @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6
          (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst))) =>
    @Eq.{max (u_1 + 1) (u_2 + 1)}
      (@LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 K)
      (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 K
        (@Top.top.{u_1} (@Subgroup.{u_1} J inst)
          (@OrderTop.toTop.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
              (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
              (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                (@Subgroup.instCompleteLattice.{u_1} J inst)))))
        (@le_top.{u_1} (@Subgroup.{u_1} J inst)
          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
          (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
              (@Subgroup.instCompleteLattice.{u_1} J inst)))
          K)
        F)
      f := by sorry
