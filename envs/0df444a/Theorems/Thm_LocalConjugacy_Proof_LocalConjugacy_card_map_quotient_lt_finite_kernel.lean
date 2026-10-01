-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_card_map_quotient_lt_finite_kernel
-- name    : LocalConjugacy.Proof.LocalConjugacy.card_map_quotient_lt_finite_kernel
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:53:18.038493+00:00
-- url     : https://prove2.me/theorems/5350f510-3fa7-4af0-99d6-007dfa774648
-- title:
--   A nontrivial quotient decreases a finite subgroup order
-- statement:
--   Let $G$ be a group, let $N\le G$ be finite, and let $D\trianglelefteq G$ be nontrivial and contained in $N$. If $\pi:G\to G/D$ is the quotient map, then
--
--   $$|\pi(N)|<|N|.$$
--
--   This supplies the strict decrease needed for induction after quotienting a finite subgroup by a nontrivial normal subgroup.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/FiniteKernelTools.lean, lines 48–70; source SHA-256 d52afafade269acd8512c3b357588ee8fbc72b6710e28852052150018abe41ea.

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

theorem LocalConjugacy.Proof.LocalConjugacy.card_map_quotient_lt_finite_kernel :
∀ {G : Type u_1} [inst : Group.{u_1} G] (N D : @Subgroup.{u_1} G inst)
  [Finite.{u_1 + 1}
      (@Subtype.{u_1 + 1} G fun (x : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)]
  [inst_2 : @Subgroup.Normal.{u_1} G inst D]
  (hDN :
    @LE.le.{u_1} (@Subgroup.{u_1} G inst)
      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
      D N)
  (hD :
    @Ne.{u_1 + 1} (@Subgroup.{u_1} G inst) D
      (@Bot.bot.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instBot.{u_1} G inst))),
  @LT.lt.{0} Nat instLTNat
    (Nat.card.{u_1}
      (@Subtype.{u_1 + 1}
        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) D)
        fun
          (x :
            @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) D) =>
        @Membership.mem.{u_1, u_1}
          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) D)
          (@Subgroup.{u_1}
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) D)
            (@QuotientGroup.Quotient.group.{u_1} G inst D inst_2))
          (@SetLike.instMembership.{u_1, u_1}
            (@Subgroup.{u_1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) D)
              (@QuotientGroup.Quotient.group.{u_1} G inst D inst_2))
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) D)
            (@Subgroup.instSetLike.{u_1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) D)
              (@QuotientGroup.Quotient.group.{u_1} G inst D inst_2)))
          (@Subgroup.map.{u_1, u_1} G inst
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) D)
            (@QuotientGroup.Quotient.group.{u_1} G inst D inst_2) (@QuotientGroup.mk'.{u_1} G inst D inst_2) N)
          x))
    (Nat.card.{u_1}
      (@Subtype.{u_1 + 1} G fun (x : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)) := by sorry
