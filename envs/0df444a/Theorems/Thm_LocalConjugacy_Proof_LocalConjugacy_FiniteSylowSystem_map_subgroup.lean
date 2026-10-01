-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_FiniteSylowSystem_map_subgroup
-- name    : LocalConjugacy.Proof.LocalConjugacy.FiniteSylowSystem.map_subgroup
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:52:08.320094+00:00
-- url     : https://prove2.me/theorems/26c2bec8-c4a9-4fec-8c87-45ccc31d8a22
-- title:
--   A compatible Sylow system has the prescribed quotient images
-- statement:
--   Let $G$ be a profinite group and $p$ a prime. For every open normal subgroup $U\trianglelefteq G$, choose a Sylow $p$-subgroup $P_U\le G/U$. Assume compatibility: whenever $U\le V$, the quotient map $G/U\to G/V$ sends $P_U$ onto $P_V$. Write $\pi_U:G\to G/U$ and define $P=\bigcap_U\pi_U^{-1}(P_U)$. Then
--
--   $$
--   \forall U\trianglelefteq_{\mathrm{open}}G,\qquad \pi_U(P)=P_U.
--   $$
--
--   This realizes a compatible family of finite Sylow subgroups as the quotient images of one subgroup of the profinite group.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/ProfiniteSylow.lean, lines 160–193; source SHA-256 5682caba9ea1362b3b946fc0d5a99e168729ce3208509e1370eea2647579d5bf.

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

theorem LocalConjugacy.Proof.LocalConjugacy.FiniteSylowSystem.map_subgroup :
∀ {G : Type u} [inst : Group.{u} G] [inst_1 : TopologicalSpace.{u} G]
  [inst_2 : @LocalConjugacy.Proof.LocalConjugacy.Profinite.{u} G inst inst_1] {p : Nat} [inst_3 : Fact (Nat.Prime p)]
  (P :
    (U : @OpenNormalSubgroup.{u} G inst inst_1) →
      @Sylow.{u} p
        (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
          (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
        (@QuotientGroup.Quotient.group.{u} G inst
          (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
          (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U)))
  (hP :
    ∀ (U V : @OpenNormalSubgroup.{u} G inst inst_1)
      (h :
        @LE.le.{u} (@OpenNormalSubgroup.{u} G inst inst_1)
          (@Preorder.toLE.{u} (@OpenNormalSubgroup.{u} G inst inst_1)
            (@PartialOrder.toPreorder.{u} (@OpenNormalSubgroup.{u} G inst inst_1)
              (@OpenNormalSubgroup.instPartialOrderOpenNormalSubgroup.{u} G inst inst_1)))
          U V),
      @Eq.{u + 1}
        (@Sylow.{u} p
          (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 V)))
          (@QuotientGroup.Quotient.group.{u} G inst
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 V))
            (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 V)))
        (@Sylow.mapSurjective.{u, u} p
          (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
          (@QuotientGroup.Quotient.group.{u} G inst
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
            (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
          (@Subgroup.instFiniteQuotientOfSeparatelyContinuousMulOfCompactSpace.{u} G inst inst_1
            (@instSeparatelyContinuousMulOfContinuousMul.{u} G inst_1
              (@MulOne.toMul.{u} G
                (@MulOneClass.toMulOne.{u} G
                  (@Monoid.toMulOneClass.{u} G (@DivInvMonoid.toMonoid.{u} G (@Group.toDivInvMonoid.{u} G inst)))))
              (@IsTopologicalGroup.toContinuousMul.{u} G inst_1 inst
                (@LocalConjugacy.Proof.LocalConjugacy.Profinite.toIsTopologicalGroup.{u} G inst inst_1 inst_2)))
            (@LocalConjugacy.Proof.LocalConjugacy.Profinite.toCompactSpace.{u} G inst inst_1 inst_2)
            (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
          (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 V)))
          (@QuotientGroup.Quotient.group.{u} G inst
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 V))
            (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 V))
          (@LocalConjugacy.Proof.LocalConjugacy.FiniteSylowSystem.transition.{u} G inst inst_1 U V h)
          (@LocalConjugacy.Proof.LocalConjugacy.FiniteSylowSystem.transition_surjective.{u} G inst inst_1 inst_2 U V h)
          inst_3 (P U))
        (P V))
  (U : @OpenNormalSubgroup.{u} G inst inst_1),
  @Eq.{u + 1}
    (@Subgroup.{u}
      (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
        (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
      (@QuotientGroup.Quotient.group.{u} G inst
        (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
        (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U)))
    (@Subgroup.map.{u, u} G inst
      (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
        (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
      (@QuotientGroup.Quotient.group.{u} G inst
        (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
        (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
      (@QuotientGroup.mk'.{u} G inst
        (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
        (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
      (@LocalConjugacy.Proof.LocalConjugacy.FiniteSylowSystem.subgroup.{u} G inst inst_1 p P))
    (@Sylow.toSubgroup.{u} p
      (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
        (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
      (@QuotientGroup.Quotient.group.{u} G inst
        (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
        (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
      (P U)) := by sorry
