-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_exists_minimal_closed_subgroup_of_chain_condition
-- name    : LocalConjugacy.Proof.LocalConjugacy.exists_minimal_closed_subgroup_of_chain_condition
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:03:06.070344+00:00
-- url     : https://prove2.me/theorems/d9e64b6d-c5a6-4b83-b72f-510b2149c86f
-- title:
--   A minimal closed intermediate subgroup from a chain condition
-- statement:
--   Let $J$ be a group equipped with a compact topology, let $P\le J$, and let $\mathcal B$ be a property of subgroups of $J$. Assume $\mathcal B(J)$. Assume also that for every nonempty family $\mathcal C$ linearly ordered by inclusion, if each $H\in\mathcal C$ is closed, contains $P$, and satisfies $\mathcal B$, then $\mathcal B(\bigcap\mathcal C)$. There exists a closed subgroup $L$ with $P\le L$ and $\mathcal B(L)$ such that
--
--   $$P\le H\le L,\quad H\text{ closed},\quad\mathcal B(H)\quad\Longrightarrow\quad H=L.$$
--
--   This is a minimality principle for closed intermediate subgroups satisfying a property preserved by nonempty chain intersections.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/CocycleZorn.lean, lines 40–60; source SHA-256 e1e12eb6db3f14e77d7b32521dedaac1aaa35f2d93a22daf6f1432f8e67d8240.

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

theorem LocalConjugacy.Proof.LocalConjugacy.exists_minimal_closed_subgroup_of_chain_condition :
∀ {J : Type u_1} [inst : Group.{u_1} J] [inst_1 : TopologicalSpace.{u_1} J] [@CompactSpace.{u_1} J inst_1]
  (P : @Subgroup.{u_1} J inst) (bad : @Subgroup.{u_1} J inst → Prop)
  (hbad : bad (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)))
  (hchain :
    ∀ (c : Set.{u_1} (@Subgroup.{u_1} J inst)),
      @Set.Nonempty.{u_1} (@Subgroup.{u_1} J inst) c →
        @IsChain.{u_1} (@Subgroup.{u_1} J inst)
            (fun (x1 x2 : @Subgroup.{u_1} J inst) =>
              @LE.le.{u_1} (@Subgroup.{u_1} J inst)
                (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                  (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
                x1 x2)
            c →
          (∀ (H : @Subgroup.{u_1} J inst),
              @Membership.mem.{u_1, u_1} (@Subgroup.{u_1} J inst) (Set.{u_1} (@Subgroup.{u_1} J inst))
                  (@Set.instMembership.{u_1} (@Subgroup.{u_1} J inst)) c H →
                And
                  (@IsClosed.{u_1} J inst_1
                    (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) H))
                  (And
                    (@LE.le.{u_1} (@Subgroup.{u_1} J inst)
                      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                          (@Subgroup.instPartialOrder.{u_1} J inst)))
                      P H)
                    (bad H))) →
            bad (@InfSet.sInf.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instInfSet.{u_1} J inst) c)),
  @Exists.{u_1 + 1} (@Subgroup.{u_1} J inst) fun (L : @Subgroup.{u_1} J inst) =>
    @Minimal.{u_1} (@Subgroup.{u_1} J inst)
      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
      (fun (H : @Subgroup.{u_1} J inst) =>
        And
          (@IsClosed.{u_1} J inst_1
            (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) H))
          (And
            (@LE.le.{u_1} (@Subgroup.{u_1} J inst)
              (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
              P H)
            (bad H)))
      L := by sorry
