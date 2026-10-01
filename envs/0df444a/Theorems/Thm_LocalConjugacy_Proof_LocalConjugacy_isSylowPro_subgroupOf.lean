-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isSylowPro_subgroupOf
-- name    : LocalConjugacy.Proof.LocalConjugacy.isSylowPro_subgroupOf
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:50:09.579874+00:00
-- url     : https://prove2.me/theorems/abfae729-dd56-4fcd-9c49-3ad3b78aafe7
-- title:
--   A relative profinite Sylow subgroup is Sylow in its domain
-- statement:
--   Let $G$ be a profinite group, $p\in\mathbb N$, and $H\le G$ a closed subgroup. Suppose $P\le H$ is closed in $G$, is pro-$p$, and is maximal among the closed pro-$p$ subgroups of $G$ contained in $H$. Regard $P$ as a subgroup $P_H$ of $H$, with the inherited topology. Then
--
--   $$
--   P_H\text{ is a maximal closed pro-}p\text{ subgroup of }H.
--   $$
--
--   This transfers the ambient-subgroup formulation of a profinite Sylow condition to the subgroup's own ambient group. The quotient-based pro-$p$ condition is used here for any natural number $p$; primality is not an assumption.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/ProfiniteSylow.lean, lines 324–341; source SHA-256 5682caba9ea1362b3b946fc0d5a99e168729ce3208509e1370eea2647579d5bf.

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

universe u

theorem LocalConjugacy.Proof.LocalConjugacy.isSylowPro_subgroupOf :
∀ {G : Type u} [inst : Group.{u} G] [inst_1 : TopologicalSpace.{u} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u} G inst inst_1] {p : Nat} (H P : @Subgroup.{u} G inst)
  (hH : @IsClosed.{u} G inst_1 (@SetLike.coe.{u, u} (@Subgroup.{u} G inst) G (@Subgroup.instSetLike.{u} G inst) H))
  (hP : @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u} p G inst inst_1 H P),
  @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u} p
    (@Subtype.{u + 1} G fun (x : G) =>
      @Membership.mem.{u, u} G (@Subgroup.{u} G inst)
        (@SetLike.instMembership.{u, u} (@Subgroup.{u} G inst) G (@Subgroup.instSetLike.{u} G inst)) H x)
    (@Subgroup.toGroup.{u} G inst H)
    (@instTopologicalSpaceSubtype.{u} G
      (fun (x : G) =>
        @Membership.mem.{u, u} G (@Subgroup.{u} G inst)
          (@SetLike.instMembership.{u, u} (@Subgroup.{u} G inst) G (@Subgroup.instSetLike.{u} G inst)) H x)
      inst_1)
    (@Top.top.{u}
      (@Subgroup.{u}
        (@Subtype.{u + 1} G fun (x : G) =>
          @Membership.mem.{u, u} G (@Subgroup.{u} G inst)
            (@SetLike.instMembership.{u, u} (@Subgroup.{u} G inst) G (@Subgroup.instSetLike.{u} G inst)) H x)
        (@Subgroup.toGroup.{u} G inst H))
      (@Subgroup.instTop.{u}
        (@Subtype.{u + 1} G fun (x : G) =>
          @Membership.mem.{u, u} G (@Subgroup.{u} G inst)
            (@SetLike.instMembership.{u, u} (@Subgroup.{u} G inst) G (@Subgroup.instSetLike.{u} G inst)) H x)
        (@Subgroup.toGroup.{u} G inst H)))
    (@Subgroup.subgroupOf.{u} G inst P H) := by sorry
