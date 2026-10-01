-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isSylowPro_of_index
-- name    : LocalConjugacy.Proof.LocalConjugacy.isSylowPro_of_index
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:51:34.074089+00:00
-- url     : https://prove2.me/theorems/e239eadc-e4a8-446c-ae2a-79162459cbf2
-- title:
--   A prime-to-$p$ index criterion for Sylow subgroups
-- statement:
--   Let $G$ be a discrete group, $p$ a prime, and $P\le J\le G$. Assume that $P$ is a $p$-group and that $p$ does not divide $[J:P]$. The index is the natural-number index, with infinite index represented by $0$, so this hypothesis also ensures that the index is finite. Then
--
--   $$P\text{ is a Sylow pro-}p\text{ subgroup of }J.$$
--
--   In the discrete topology this means that $P$ is maximal among $p$-subgroups of $J$. The criterion allows the ambient group and $P$ to be infinite.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/FiniteSylow.lean, lines 18–34; source SHA-256 a7fbd4b9a6cc5de0fa5a8b4b4793e40168514fcd4df9ad142bce5dfc17aee6c0.

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

theorem LocalConjugacy.Proof.LocalConjugacy.isSylowPro_of_index :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G] [@DiscreteTopology.{u_1} G inst_1] {p : Nat}
  [Fact (Nat.Prime p)] (J P : @Subgroup.{u_1} G inst)
  (hPJ :
    @LE.le.{u_1} (@Subgroup.{u_1} G inst)
      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
      P J)
  (hP :
    @IsPGroup.{u_1} p
      (@Subtype.{u_1 + 1} G fun (x : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) P x)
      (@Subgroup.toGroup.{u_1} G inst P))
  (hindex :
    Not
      (@Dvd.dvd.{0} Nat Nat.instDvd p
        (@Subgroup.index.{u_1}
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) J x)
          (@Subgroup.toGroup.{u_1} G inst J) (@Subgroup.subgroupOf.{u_1} G inst P J)))),
  @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1} p G inst inst_1 J P := by sorry
