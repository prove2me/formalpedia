-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_isProP_of_quotient_images
-- name    : LocalConjugacy.Proof.LocalConjugacy.isProP_of_quotient_images
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:51:58.706624+00:00
-- url     : https://prove2.me/theorems/283d4ec4-ff13-4d63-8400-f38db15282ad
-- title:
--   Detecting pro-$p$ subgroups in finite quotient images
-- statement:
--   Let $G$ be a profinite group, $H\le G$ any subgroup with its induced topology, and $p\in\mathbb N$. Suppose that the image of $H$ in $G/U$ is a $p$-group for every open normal subgroup $U$ of $G$. Then
--
--   $$H\text{ is pro-}p.$$
--
--   Here, for an arbitrary natural number $p$, a $p$-group means that every element is killed by some power $p^n$; pro-$p$ means that every quotient by an open normal subgroup is a $p$-group. This criterion transfers information from ambient finite quotients to the intrinsic quotients of $H$.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/ProfiniteSylow.lean, lines 34–48; source SHA-256 5682caba9ea1362b3b946fc0d5a99e168729ce3208509e1370eea2647579d5bf.

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

theorem LocalConjugacy.Proof.LocalConjugacy.isProP_of_quotient_images :
∀ {G : Type u} [inst : Group.{u} G] [inst_1 : TopologicalSpace.{u} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u} G inst inst_1] {p : Nat} (H : @Subgroup.{u} G inst)
  (h :
    ∀ (U : @OpenNormalSubgroup.{u} G inst inst_1),
      @IsPGroup.{u} p
        (@Subtype.{u + 1}
          (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
          fun
            (x :
              @HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
                (@OpenSubgroup.toSubgroup.{u} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))) =>
          @Membership.mem.{u, u}
            (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
              (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
            (@Subgroup.{u}
              (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
                (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
              (@QuotientGroup.Quotient.group.{u} G inst
                (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
                (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U)))
            (@SetLike.instMembership.{u, u}
              (@Subgroup.{u}
                (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
                  (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
                (@QuotientGroup.Quotient.group.{u} G inst
                  (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U)))
              (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
                (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
              (@Subgroup.instSetLike.{u}
                (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
                  (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
                (@QuotientGroup.Quotient.group.{u} G inst
                  (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))))
            (@Subgroup.map.{u, u} G inst
              (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
                (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
              (@QuotientGroup.Quotient.group.{u} G inst
                (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
                (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
              (@QuotientGroup.mk'.{u} G inst
                (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
                (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
              H)
            x)
        (@Subgroup.toGroup.{u}
          (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
          (@QuotientGroup.Quotient.group.{u} G inst
            (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
            (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
          (@Subgroup.map.{u, u} G inst
            (@HasQuotient.Quotient.{u, u} G (@Subgroup.{u} G inst) (@QuotientGroup.instHasQuotientSubgroup.{u} G inst)
              (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U)))
            (@QuotientGroup.Quotient.group.{u} G inst
              (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
              (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
            (@QuotientGroup.mk'.{u} G inst
              (@OpenSubgroup.toSubgroup.{u} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u} G inst inst_1 U))
              (@OpenNormalSubgroup.instNormal.{u} G inst inst_1 U))
            H))),
  @LocalConjugacy.Proof.LocalConjugacy.IsProP.{u} p
    (@Subtype.{u + 1} G fun (x : G) =>
      @Membership.mem.{u, u} G (@Subgroup.{u} G inst)
        (@SetLike.instMembership.{u, u} (@Subgroup.{u} G inst) G (@Subgroup.instSetLike.{u} G inst)) H x)
    (@Subgroup.toGroup.{u} G inst H)
    (@instTopologicalSpaceSubtype.{u} G
      (fun (x : G) =>
        @Membership.mem.{u, u} G (@Subgroup.{u} G inst)
          (@SetLike.instMembership.{u, u} (@Subgroup.{u} G inst) G (@Subgroup.instSetLike.{u} G inst)) H x)
      inst_1) := by sorry
