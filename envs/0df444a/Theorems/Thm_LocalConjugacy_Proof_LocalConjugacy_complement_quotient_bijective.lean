-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_complement_quotient_bijective
-- name    : LocalConjugacy.Proof.LocalConjugacy.complement_quotient_bijective
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:53:32.894982+00:00
-- url     : https://prove2.me/theorems/1d6e40b4-aef0-47cc-b1c9-c10ca2c2a9d3
-- title:
--   A complement maps bijectively to the quotient
-- statement:
--   Let $G$ be a group, $N\trianglelefteq G$, and $K\le G$. Suppose every element of $G$ can be written as $nk$ with $n\in N$, $k\in K$, and suppose $N\cap K=1$. Then
--
--   $$
--   K\longrightarrow G/N,\qquad k\longmapsto kN
--   $$
--
--   is bijective.
--
--   This identifies a complement to a normal subgroup with the corresponding quotient group.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/ComplementConjugacy.lean, lines 68–86; source SHA-256 db23ca50182cb43f665f9e47655351cb20719e0f1f70eb0e72c7d9840a6e7b2a.

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

theorem LocalConjugacy.Proof.LocalConjugacy.complement_quotient_bijective :
∀ {G : Type u_1} [inst : Group.{u_1} G] (N K : @Subgroup.{u_1} G inst) [inst_1 : @Subgroup.Normal.{u_1} G inst N]
  (hs : @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N K)
  (hd :
    @Eq.{u_1 + 1} (@Subgroup.{u_1} G inst)
      (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N K)
      (@Bot.bot.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instBot.{u_1} G inst))),
  @Function.Bijective.{u_1 + 1, u_1 + 1}
    (@Subtype.{u_1 + 1} G fun (x : G) =>
      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K x)
    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
      N)
    (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
      (@MonoidHom.{u_1, u_1}
        (@Subtype.{u_1 + 1} G fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K x)
        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) N)
        (@MulOneClass.toMulOne.{u_1}
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K x)
          (@Monoid.toMulOneClass.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K
                x)
            (@DivInvMonoid.toMonoid.{u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K
                  x)
              (@Group.toDivInvMonoid.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    K x)
                (@Subgroup.toGroup.{u_1} G inst K)))))
        (@MulOneClass.toMulOne.{u_1}
          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) N)
          (@Monoid.toMulOneClass.{u_1}
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) N)
            (@DivInvMonoid.toMonoid.{u_1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) N)
              (@Group.toDivInvMonoid.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) N)
                (@QuotientGroup.Quotient.group.{u_1} G inst N inst_1))))))
      (@Subtype.{u_1 + 1} G fun (x : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K x)
      (fun
          (x :
            @Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K
                x) =>
        @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) N)
      (@MonoidHom.instFunLike.{u_1, u_1}
        (@Subtype.{u_1 + 1} G fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K x)
        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) N)
        (@MulOneClass.toMulOne.{u_1}
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K x)
          (@Monoid.toMulOneClass.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K
                x)
            (@DivInvMonoid.toMonoid.{u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K
                  x)
              (@Group.toDivInvMonoid.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    K x)
                (@Subgroup.toGroup.{u_1} G inst K)))))
        (@MulOneClass.toMulOne.{u_1}
          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) N)
          (@Monoid.toMulOneClass.{u_1}
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) N)
            (@DivInvMonoid.toMonoid.{u_1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) N)
              (@Group.toDivInvMonoid.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) N)
                (@QuotientGroup.Quotient.group.{u_1} G inst N inst_1))))))
      (@MonoidHom.comp.{u_1, u_1, u_1}
        (@Subtype.{u_1 + 1} G fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K x)
        G
        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) N)
        (@MulOneClass.toMulOne.{u_1}
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K x)
          (@Monoid.toMulOneClass.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K
                x)
            (@DivInvMonoid.toMonoid.{u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) K
                  x)
              (@Group.toDivInvMonoid.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    K x)
                (@Subgroup.toGroup.{u_1} G inst K)))))
        (@MulOneClass.toMulOne.{u_1} G
          (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))
        (@MulOneClass.toMulOne.{u_1}
          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) N)
          (@Monoid.toMulOneClass.{u_1}
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) N)
            (@DivInvMonoid.toMonoid.{u_1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) N)
              (@Group.toDivInvMonoid.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) N)
                (@QuotientGroup.Quotient.group.{u_1} G inst N inst_1)))))
        (@QuotientGroup.mk'.{u_1} G inst N inst_1) (@Subgroup.subtype.{u_1} G inst K))) := by sorry
