-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isSylowPro_of_full_images
-- name    : LocalConjugacy.Proof.LocalConjugacy.isSylowPro_of_full_images
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:54:15.830414+00:00
-- url     : https://prove2.me/theorems/03a24027-f0c9-4228-9206-4a3b252d6d23
-- title:
--   Full finite Sylow images imply the profinite Sylow condition
-- statement:
--   Let $G$ be a profinite group, $p\in\mathbb N$, and $P\le G$ a closed subgroup. Assume that for every open normal subgroup $U\trianglelefteq G$, the image of $P$ in $G/U$ is a Sylow $p$-subgroup. Then
--
--   $$
--   P\text{ is a maximal closed pro-}p\text{ subgroup of }G.
--   $$
--
--   This recognizes the profinite Sylow condition from all finite quotient images. The formal statement uses the quotient-based pro-$p$ and Sylow definitions for arbitrary natural $p$ and has no separate primality hypothesis.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/ProfiniteSylow.lean, lines 231–254; source SHA-256 5682caba9ea1362b3b946fc0d5a99e168729ce3208509e1370eea2647579d5bf.

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

theorem LocalConjugacy.Proof.LocalConjugacy.isSylowPro_of_full_images :
∀ {G : Type u} [inst : Group.{u} G] [inst_1 : TopologicalSpace.{u} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u} G inst inst_1] {p : Nat} (P : @Subgroup.{u} G inst)
  (hP : @IsClosed.{u} G inst_1 (@SetLike.coe.{u, u} (@Subgroup.{u} G inst) G (@Subgroup.instSetLike.{u} G inst) P))
  (hfull :
    ∀ (U : @OpenNormalSubgroup.{u} G inst inst_1),
      @Exists.{u + 1}
        (@Sylow.{u} p
          (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
          (@QuotientGroup.Quotient.group.{u} G inst
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
            (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U)))
        fun
          (S :
            @Sylow.{u} p
              (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
                (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
              (@QuotientGroup.Quotient.group.{u} G inst
                (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
                (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))) =>
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
            P)
          (@Sylow.toSubgroup.{u} p
            (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
              (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
            (@QuotientGroup.Quotient.group.{u} G inst
              (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
              (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
            S)),
  @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u} p G inst inst_1
    (@Top.top.{u} (@Subgroup.{u} G inst) (@Subgroup.instTop.{u} G inst)) P := by sorry
