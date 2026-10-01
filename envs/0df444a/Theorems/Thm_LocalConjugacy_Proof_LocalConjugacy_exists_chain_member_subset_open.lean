-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_exists_chain_member_subset_open
-- name    : LocalConjugacy.Proof.LocalConjugacy.exists_chain_member_subset_open
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:53:13.11273+00:00
-- url     : https://prove2.me/theorems/134799ee-bf66-496a-b443-143acf0e01be
-- title:
--   A chain member lies in an open neighborhood of the intersection
-- statement:
--   Let $J$ be a group endowed with a compact topology. Let $\mathcal C$ be a nonempty collection of closed subgroups of $J$ that is totally ordered by inclusion. If an open set $O\subseteq J$ contains $\bigcap_{H\in\mathcal C}H$, then
--
--   $$\exists H\in\mathcal C,\qquad H\subseteq O.$$
--
--   This compactness statement applies to chains of arbitrary cardinality and supports minimal-subgroup arguments for continuous cocycles.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/CocycleZorn.lean, lines 15–38; source SHA-256 e1e12eb6db3f14e77d7b32521dedaac1aaa35f2d93a22daf6f1432f8e67d8240.

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

theorem LocalConjugacy.Proof.LocalConjugacy.exists_chain_member_subset_open :
∀ {J : Type u_1} [inst : Group.{u_1} J] [inst_1 : TopologicalSpace.{u_1} J] [@CompactSpace.{u_1} J inst_1]
  (c : Set.{u_1} (@Subgroup.{u_1} J inst)) (hne : @Set.Nonempty.{u_1} (@Subgroup.{u_1} J inst) c)
  (hc :
    @IsChain.{u_1} (@Subgroup.{u_1} J inst)
      (fun (x1 x2 : @Subgroup.{u_1} J inst) =>
        @LE.le.{u_1} (@Subgroup.{u_1} J inst)
          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
          x1 x2)
      c)
  (hclosed :
    ∀ (H : @Subgroup.{u_1} J inst),
      @Membership.mem.{u_1, u_1} (@Subgroup.{u_1} J inst) (Set.{u_1} (@Subgroup.{u_1} J inst))
          (@Set.instMembership.{u_1} (@Subgroup.{u_1} J inst)) c H →
        @IsClosed.{u_1} J inst_1
          (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) H))
  (O : Set.{u_1} J) (hO : @IsOpen.{u_1} J inst_1 O)
  (hsub :
    @LE.le.{u_1} (Set.{u_1} J) (@Set.instLE.{u_1} J)
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)
        (@InfSet.sInf.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instInfSet.{u_1} J inst) c))
      O),
  @Exists.{u_1 + 1} (@Subgroup.{u_1} J inst) fun (H : @Subgroup.{u_1} J inst) =>
    And
      (@Membership.mem.{u_1, u_1} (@Subgroup.{u_1} J inst) (Set.{u_1} (@Subgroup.{u_1} J inst))
        (@Set.instMembership.{u_1} (@Subgroup.{u_1} J inst)) c H)
      (@LE.le.{u_1} (Set.{u_1} J) (@Set.instLE.{u_1} J)
        (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) H) O) := by sorry
