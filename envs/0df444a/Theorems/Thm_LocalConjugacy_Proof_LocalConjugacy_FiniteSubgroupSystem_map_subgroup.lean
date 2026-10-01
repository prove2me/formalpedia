-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_FiniteSubgroupSystem_map_subgroup
-- name    : LocalConjugacy.Proof.LocalConjugacy.FiniteSubgroupSystem.map_subgroup
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:50:28.982792+00:00
-- url     : https://prove2.me/theorems/e5c9f399-f40d-49e6-8c00-3ea6a4cc0ce0
-- title:
--   Recovering the images of a compatible subgroup system
-- statement:
--   Let $G$ be a profinite group. For each open normal subgroup $U\trianglelefteq G$, choose a subgroup $S_U\le G/U$. Assume compatibility: whenever $U\le V$, the natural map $G/U\to G/V$ sends $S_U$ onto $S_V$. Let $q_U:G\to G/U$ be the quotient map and set $S=\bigcap_U q_U^{-1}(S_U)$. Then, for every open normal $U$,
--
--   $$q_U(S)=S_U.$$
--
--   Thus a compatible system of finite quotient subgroups is realized by a subgroup with precisely the prescribed images.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/ProfiniteHall.lean, lines 49–82; source SHA-256 5bc8b50236c68c4f09b947c789183f5f2267a1734ba468b979d7ad6168ba9c97.

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

theorem LocalConjugacy.Proof.LocalConjugacy.FiniteSubgroupSystem.map_subgroup :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1]
  (S :
    (U : @OpenNormalSubgroup.{u_1} G inst inst_1) →
      @Subgroup.{u_1}
        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
        (@QuotientGroup.Quotient.group.{u_1} G inst
          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
  (hS :
    ∀ (U V : @OpenNormalSubgroup.{u_1} G inst inst_1)
      (h :
        @LE.le.{u_1} (@OpenNormalSubgroup.{u_1} G inst inst_1)
          (@Preorder.toLE.{u_1} (@OpenNormalSubgroup.{u_1} G inst inst_1)
            (@PartialOrder.toPreorder.{u_1} (@OpenNormalSubgroup.{u_1} G inst inst_1)
              (@OpenNormalSubgroup.instPartialOrderOpenNormalSubgroup.{u_1} G inst inst_1)))
          U V),
      @Eq.{u_1 + 1}
        (@Subgroup.{u_1}
          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V)))
          (@QuotientGroup.Quotient.group.{u_1} G inst
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V))
            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 V)))
        (@Subgroup.map.{u_1, u_1}
          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
          (@QuotientGroup.Quotient.group.{u_1} G inst
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V)))
          (@QuotientGroup.Quotient.group.{u_1} G inst
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V))
            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 V))
          (@LocalConjugacy.Proof.LocalConjugacy.FiniteSylowSystem.transition.{u_1} G inst inst_1 U V h) (S U))
        (S V))
  (U : @OpenNormalSubgroup.{u_1} G inst inst_1),
  @Eq.{u_1 + 1}
    (@Subgroup.{u_1}
      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
      (@QuotientGroup.Quotient.group.{u_1} G inst
        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
    (@Subgroup.map.{u_1, u_1} G inst
      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
      (@QuotientGroup.Quotient.group.{u_1} G inst
        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
      (@QuotientGroup.mk'.{u_1} G inst
        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
      (@LocalConjugacy.Proof.LocalConjugacy.FiniteSubgroupSystem.subgroup.{u_1} G inst inst_1 S))
    (S U) := by sorry
