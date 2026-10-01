-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_card_intertwiners
-- name    : LocalConjugacy.Proof.LocalConjugacy.card_intertwiners
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:52:39.429458+00:00
-- url     : https://prove2.me/theorems/87fd113e-07a2-46d3-9462-265a8aa29f2a
-- title:
--   A nonempty intertwiner set has prime-power cardinality
-- statement:
--   Let $J$ and $N$ be groups equipped with topologies, and let $J$ act on $N$ by automorphisms. Suppose $p$ is prime and $N$ is a finite $p$-group. Let $K\le J$ and let $f,g:J\to N$ be continuous cocycles. Define
--
--   $$
--   T=\{n\in N:\ \forall x\in K,\ g(x)=n^{-1}f(x)(x\cdot n)\}.
--   $$
--
--   If a specified $n_0\in N$ belongs to $T$, then
--
--   $$
--   \exists k\in\mathbb N,\qquad |T|=p^k.
--   $$
--
--   Equivalently, $T$ is the fixed-point set for the $K$-action $x*n=f(x)(x\cdot n)g(x)^{-1}$. The cardinality statement supports coprime fixed-point arguments for cocycle intertwiners.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/CocycleInjectivity.lean, lines 47–78; source SHA-256 d4e86515de94d55aa0fb1229c0812d13f3e78bed333308419e8dbeaa37a6edde.

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

theorem LocalConjugacy.Proof.LocalConjugacy.card_intertwiners :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [inst_3 : TopologicalSpace.{u_2} N]
  [inst_4 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  {p : Nat} [Fact (Nat.Prime p)] [Finite.{u_2 + 1} N] (hN : @IsPGroup.{u_2} p N inst_1) (K : @Subgroup.{u_1} J inst)
  (f g :
    @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)))
  (n₀ : N)
  (hn₀ :
    ∀
      (x :
        @Subtype.{u_1 + 1} J fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) K x),
      @Eq.{u_2 + 1} N
        (@LocalConjugacy.Cocycle.toFun.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4
          (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) g
          (@Subtype.mk.{u_1 + 1} J
            (fun (x : J) =>
              @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst))
                (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) x)
            (@Subtype.val.{u_1 + 1} J
              (fun (x : J) =>
                @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) K
                  x)
              x)
            trivial))
        (@HMul.hMul.{u_2, u_2, u_2} N N N
          (@instHMul.{u_2} N
            (@MulOne.toMul.{u_2} N
              (@MulOneClass.toMulOne.{u_2} N
                (@Monoid.toMulOneClass.{u_2} N
                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
          (@HMul.hMul.{u_2, u_2, u_2} N N N
            (@instHMul.{u_2} N
              (@MulOne.toMul.{u_2} N
                (@MulOneClass.toMulOne.{u_2} N
                  (@Monoid.toMulOneClass.{u_2} N
                    (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
            (@Inv.inv.{u_2} N
              (@InvOneClass.toInv.{u_2} N
                (@DivInvOneMonoid.toInvOneClass.{u_2} N
                  (@DivisionMonoid.toDivInvOneMonoid.{u_2} N (@Group.toDivisionMonoid.{u_2} N inst_1))))
              n₀)
            (@LocalConjugacy.Cocycle.toFun.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4
              (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) f
              (@Subtype.mk.{u_1 + 1} J
                (fun (x : J) =>
                  @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst))
                    (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) x)
                (@Subtype.val.{u_1 + 1} J
                  (fun (x : J) =>
                    @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J
                        (@Subgroup.instSetLike.{u_1} J inst))
                      K x)
                  x)
                trivial)))
          (@HSMul.hSMul.{u_1, u_2, u_2} J N N
            (@instHSMul.{u_1, u_2} J N
              (@SemigroupAction.toSMul.{u_1, u_2} J N
                (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
                (@MulAction.toSemigroupAction.{u_1, u_2} J N
                  (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                  (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
                    (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                    (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_4))))
            (@Subtype.val.{u_1 + 1} J
              (fun (x : J) =>
                @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) K
                  x)
              x)
            n₀))),
  @Exists.{1} Nat fun (k : Nat) =>
    @Eq.{1} Nat
      (Nat.card.{u_2}
        (@Set.Elem.{u_2} N
          (@MulAction.fixedPoints.{u_1, u_2}
            (@Subtype.{u_1 + 1} J fun (x : J) =>
              @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) K
                x)
            N
            (@DivInvMonoid.toMonoid.{u_1}
              (@Subtype.{u_1 + 1} J fun (x : J) =>
                @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) K
                  x)
              (@Group.toDivInvMonoid.{u_1}
                (@Subtype.{u_1 + 1} J fun (x : J) =>
                  @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst))
                    K x)
                (@Subgroup.toGroup.{u_1} J inst K)))
            (@Subgroup.instMulAction.{u_1, u_2} J N inst
              (@LocalConjugacy.Proof.LocalConjugacy.intertwiningAction.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4 f
                g)
              K))))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) p k) := by sorry
