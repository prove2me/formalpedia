-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_subgroup_quotient_factors
-- name    : LocalConjugacy.Proof.LocalConjugacy.subgroup_quotient_factors
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:08:08.597163+00:00
-- url     : https://prove2.me/theorems/266efe76-4027-4719-be3a-78bc6d0bd06a
-- title:
--   A subgroup quotient is an image of an ambient finite quotient
-- statement:
--   Let $G$ be profinite, let $H\le G$ be any subgroup with its inherited topology, and let $V$ be an open normal subgroup of $H$. There exist an open normal subgroup $U$ of $G$ and a surjective homomorphism
--
--   $$f:\pi_U(H)\twoheadrightarrow H/V,$$
--
--   where $\pi_U:G\to G/U$ is the quotient map.
--
--   This realizes a quotient of a subgroup as a homomorphic image of its image in an ambient finite quotient, allowing finite structural properties to be inherited by subgroups.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/SupersolvableReductions.lean, lines 106–126; source SHA-256 29509bd9dc03344a0acef30e2bd052c64781f5f1093f7c226e23a6aa0ad6969d.

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

theorem LocalConjugacy.Proof.LocalConjugacy.subgroup_quotient_factors :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1] (H : @Subgroup.{u_1} G inst)
  (V :
    @OpenNormalSubgroup.{u_1}
      (@Subtype.{u_1 + 1} G fun (x : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H x)
      (@Subgroup.toGroup.{u_1} G inst H)
      (@instTopologicalSpaceSubtype.{u_1} G
        (fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H x)
        inst_1)),
  @Exists.{u_1 + 1} (@OpenNormalSubgroup.{u_1} G inst inst_1) fun (U : @OpenNormalSubgroup.{u_1} G inst inst_1) =>
    @Exists.{u_1 + 1}
      (@MonoidHom.{u_1, u_1}
        (@Subtype.{u_1 + 1}
          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
          fun
            (x :
              @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
          @Membership.mem.{u_1, u_1}
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
            (@Subgroup.{u_1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@QuotientGroup.Quotient.group.{u_1} G inst
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
            (@SetLike.instMembership.{u_1, u_1}
              (@Subgroup.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@QuotientGroup.Quotient.group.{u_1} G inst
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@Subgroup.instSetLike.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@QuotientGroup.Quotient.group.{u_1} G inst
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
            (@Subgroup.map.{u_1, u_1} G inst
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@QuotientGroup.Quotient.group.{u_1} G inst
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
              (@QuotientGroup.mk'.{u_1} G inst
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
              H)
            x)
        (@HasQuotient.Quotient.{u_1, u_1}
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H x)
          (@Subgroup.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                x)
            (@Subgroup.toGroup.{u_1} G inst H))
          (@QuotientGroup.instHasQuotientSubgroup.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                x)
            (@Subgroup.toGroup.{u_1} G inst H))
          (@OpenSubgroup.toSubgroup.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                x)
            (@Subgroup.toGroup.{u_1} G inst H)
            (@instTopologicalSpaceSubtype.{u_1} G
              (fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              inst_1)
            (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              (@Subgroup.toGroup.{u_1} G inst H)
              (@instTopologicalSpaceSubtype.{u_1} G
                (fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                inst_1)
              V)))
        (@MulOneClass.toMulOne.{u_1}
          (@Subtype.{u_1 + 1}
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
            fun
              (x :
                @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
            @Membership.mem.{u_1, u_1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@Subgroup.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@QuotientGroup.Quotient.group.{u_1} G inst
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
              (@SetLike.instMembership.{u_1, u_1}
                (@Subgroup.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@Subgroup.instSetLike.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
              (@Subgroup.map.{u_1, u_1} G inst
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@QuotientGroup.Quotient.group.{u_1} G inst
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                (@QuotientGroup.mk'.{u_1} G inst
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                H)
              x)
          (@Monoid.toMulOneClass.{u_1}
            (@Subtype.{u_1 + 1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              fun
                (x :
                  @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
              @Membership.mem.{u_1, u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@Subgroup.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                (@SetLike.instMembership.{u_1, u_1}
                  (@Subgroup.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@Subgroup.instSetLike.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
                (@Subgroup.map.{u_1, u_1} G inst
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                  (@QuotientGroup.mk'.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                  H)
                x)
            (@DivInvMonoid.toMonoid.{u_1}
              (@Subtype.{u_1 + 1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                fun
                  (x :
                    @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                @Membership.mem.{u_1, u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@Subgroup.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                  (@SetLike.instMembership.{u_1, u_1}
                    (@Subgroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@Subgroup.instSetLike.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
                  (@Subgroup.map.{u_1, u_1} G inst
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                    (@QuotientGroup.mk'.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                    H)
                  x)
              (@Group.toDivInvMonoid.{u_1}
                (@Subtype.{u_1 + 1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  fun
                    (x :
                      @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                  @Membership.mem.{u_1, u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@Subgroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                    (@SetLike.instMembership.{u_1, u_1}
                      (@Subgroup.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@Subgroup.instSetLike.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
                    (@Subgroup.map.{u_1, u_1} G inst
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                      (@QuotientGroup.mk'.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                      H)
                    x)
                (@Subgroup.toGroup.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                  (@Subgroup.map.{u_1, u_1} G inst
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                    (@QuotientGroup.mk'.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                    H))))))
        (@MulOneClass.toMulOne.{u_1}
          (@HasQuotient.Quotient.{u_1, u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                x)
            (@Subgroup.{u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              (@Subgroup.toGroup.{u_1} G inst H))
            (@QuotientGroup.instHasQuotientSubgroup.{u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              (@Subgroup.toGroup.{u_1} G inst H))
            (@OpenSubgroup.toSubgroup.{u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              (@Subgroup.toGroup.{u_1} G inst H)
              (@instTopologicalSpaceSubtype.{u_1} G
                (fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                inst_1)
              (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H)
                (@instTopologicalSpaceSubtype.{u_1} G
                  (fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  inst_1)
                V)))
          (@Monoid.toMulOneClass.{u_1}
            (@HasQuotient.Quotient.{u_1, u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              (@Subgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H))
              (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H))
              (@OpenSubgroup.toSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H)
                (@instTopologicalSpaceSubtype.{u_1} G
                  (fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  inst_1)
                (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H)
                  (@instTopologicalSpaceSubtype.{u_1} G
                    (fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    inst_1)
                  V)))
            (@DivInvMonoid.toMonoid.{u_1}
              (@HasQuotient.Quotient.{u_1, u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H))
                (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H))
                (@OpenSubgroup.toSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H)
                  (@instTopologicalSpaceSubtype.{u_1} G
                    (fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    inst_1)
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H)
                    (@instTopologicalSpaceSubtype.{u_1} G
                      (fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      inst_1)
                    V)))
              (@Group.toDivInvMonoid.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H))
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H))
                  (@OpenSubgroup.toSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H)
                    (@instTopologicalSpaceSubtype.{u_1} G
                      (fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      inst_1)
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@instTopologicalSpaceSubtype.{u_1} G
                        (fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        inst_1)
                      V)))
                (@QuotientGroup.Quotient.group.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H)
                  (@OpenSubgroup.toSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H)
                    (@instTopologicalSpaceSubtype.{u_1} G
                      (fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      inst_1)
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@instTopologicalSpaceSubtype.{u_1} G
                        (fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        inst_1)
                      V))
                  (@OpenNormalSubgroup.instNormal.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H)
                    (@instTopologicalSpaceSubtype.{u_1} G
                      (fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      inst_1)
                    V)))))))
      fun
        (f :
          @MonoidHom.{u_1, u_1}
            (@Subtype.{u_1 + 1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              fun
                (x :
                  @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
              @Membership.mem.{u_1, u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@Subgroup.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                (@SetLike.instMembership.{u_1, u_1}
                  (@Subgroup.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@Subgroup.instSetLike.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
                (@Subgroup.map.{u_1, u_1} G inst
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                  (@QuotientGroup.mk'.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                  H)
                x)
            (@HasQuotient.Quotient.{u_1, u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              (@Subgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H))
              (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H))
              (@OpenSubgroup.toSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H)
                (@instTopologicalSpaceSubtype.{u_1} G
                  (fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  inst_1)
                (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H)
                  (@instTopologicalSpaceSubtype.{u_1} G
                    (fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    inst_1)
                  V)))
            (@MulOneClass.toMulOne.{u_1}
              (@Subtype.{u_1 + 1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                fun
                  (x :
                    @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                @Membership.mem.{u_1, u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@Subgroup.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                  (@SetLike.instMembership.{u_1, u_1}
                    (@Subgroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@Subgroup.instSetLike.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
                  (@Subgroup.map.{u_1, u_1} G inst
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                    (@QuotientGroup.mk'.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                    H)
                  x)
              (@Monoid.toMulOneClass.{u_1}
                (@Subtype.{u_1 + 1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  fun
                    (x :
                      @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                  @Membership.mem.{u_1, u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@Subgroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                    (@SetLike.instMembership.{u_1, u_1}
                      (@Subgroup.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@Subgroup.instSetLike.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
                    (@Subgroup.map.{u_1, u_1} G inst
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                      (@QuotientGroup.mk'.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                      H)
                    x)
                (@DivInvMonoid.toMonoid.{u_1}
                  (@Subtype.{u_1 + 1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    fun
                      (x :
                        @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                    @Membership.mem.{u_1, u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@Subgroup.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                      (@SetLike.instMembership.{u_1, u_1}
                        (@Subgroup.{u_1}
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@Subgroup.instSetLike.{u_1}
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
                      (@Subgroup.map.{u_1, u_1} G inst
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                        (@QuotientGroup.mk'.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                        H)
                      x)
                  (@Group.toDivInvMonoid.{u_1}
                    (@Subtype.{u_1 + 1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      fun
                        (x :
                          @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                      @Membership.mem.{u_1, u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@Subgroup.{u_1}
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                        (@SetLike.instMembership.{u_1, u_1}
                          (@Subgroup.{u_1}
                            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                            (@QuotientGroup.Quotient.group.{u_1} G inst
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                              (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@Subgroup.instSetLike.{u_1}
                            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                            (@QuotientGroup.Quotient.group.{u_1} G inst
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                              (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
                        (@Subgroup.map.{u_1, u_1} G inst
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                          (@QuotientGroup.mk'.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                          H)
                        x)
                    (@Subgroup.toGroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                      (@Subgroup.map.{u_1, u_1} G inst
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                        (@QuotientGroup.mk'.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                        H))))))
            (@MulOneClass.toMulOne.{u_1}
              (@HasQuotient.Quotient.{u_1, u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H))
                (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H))
                (@OpenSubgroup.toSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H)
                  (@instTopologicalSpaceSubtype.{u_1} G
                    (fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    inst_1)
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H)
                    (@instTopologicalSpaceSubtype.{u_1} G
                      (fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      inst_1)
                    V)))
              (@Monoid.toMulOneClass.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H))
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H))
                  (@OpenSubgroup.toSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H)
                    (@instTopologicalSpaceSubtype.{u_1} G
                      (fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      inst_1)
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@instTopologicalSpaceSubtype.{u_1} G
                        (fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        inst_1)
                      V)))
                (@DivInvMonoid.toMonoid.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H))
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H))
                    (@OpenSubgroup.toSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@instTopologicalSpaceSubtype.{u_1} G
                        (fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        inst_1)
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        V)))
                  (@Group.toDivInvMonoid.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H))
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H))
                      (@OpenSubgroup.toSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                          (@Subtype.{u_1 + 1} G fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          (@Subgroup.toGroup.{u_1} G inst H)
                          (@instTopologicalSpaceSubtype.{u_1} G
                            (fun (x : G) =>
                              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                  (@Subgroup.instSetLike.{u_1} G inst))
                                H x)
                            inst_1)
                          V)))
                    (@QuotientGroup.Quotient.group.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@OpenSubgroup.toSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                          (@Subtype.{u_1 + 1} G fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          (@Subgroup.toGroup.{u_1} G inst H)
                          (@instTopologicalSpaceSubtype.{u_1} G
                            (fun (x : G) =>
                              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                  (@Subgroup.instSetLike.{u_1} G inst))
                                H x)
                            inst_1)
                          V))
                      (@OpenNormalSubgroup.instNormal.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        V))))))) =>
      @Function.Surjective.{u_1 + 1, u_1 + 1}
        (@Subtype.{u_1 + 1}
          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
          fun
            (x :
              @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
          @Membership.mem.{u_1, u_1}
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
            (@Subgroup.{u_1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@QuotientGroup.Quotient.group.{u_1} G inst
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
            (@SetLike.instMembership.{u_1, u_1}
              (@Subgroup.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@QuotientGroup.Quotient.group.{u_1} G inst
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@Subgroup.instSetLike.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@QuotientGroup.Quotient.group.{u_1} G inst
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
            (@Subgroup.map.{u_1, u_1} G inst
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@QuotientGroup.Quotient.group.{u_1} G inst
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
              (@QuotientGroup.mk'.{u_1} G inst
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
              H)
            x)
        (@HasQuotient.Quotient.{u_1, u_1}
          (@Subtype.{u_1 + 1} G fun (x : G) =>
            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H x)
          (@Subgroup.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                x)
            (@Subgroup.toGroup.{u_1} G inst H))
          (@QuotientGroup.instHasQuotientSubgroup.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                x)
            (@Subgroup.toGroup.{u_1} G inst H))
          (@OpenSubgroup.toSubgroup.{u_1}
            (@Subtype.{u_1 + 1} G fun (x : G) =>
              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                x)
            (@Subgroup.toGroup.{u_1} G inst H)
            (@instTopologicalSpaceSubtype.{u_1} G
              (fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              inst_1)
            (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              (@Subgroup.toGroup.{u_1} G inst H)
              (@instTopologicalSpaceSubtype.{u_1} G
                (fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                inst_1)
              V)))
        (@DFunLike.coe.{u_1 + 1, u_1 + 1, u_1 + 1}
          (@MonoidHom.{u_1, u_1}
            (@Subtype.{u_1 + 1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              fun
                (x :
                  @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
              @Membership.mem.{u_1, u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@Subgroup.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                (@SetLike.instMembership.{u_1, u_1}
                  (@Subgroup.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@Subgroup.instSetLike.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
                (@Subgroup.map.{u_1, u_1} G inst
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                  (@QuotientGroup.mk'.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                  H)
                x)
            (@HasQuotient.Quotient.{u_1, u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              (@Subgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H))
              (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H))
              (@OpenSubgroup.toSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H)
                (@instTopologicalSpaceSubtype.{u_1} G
                  (fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  inst_1)
                (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H)
                  (@instTopologicalSpaceSubtype.{u_1} G
                    (fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    inst_1)
                  V)))
            (@MulOneClass.toMulOne.{u_1}
              (@Subtype.{u_1 + 1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                fun
                  (x :
                    @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                @Membership.mem.{u_1, u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@Subgroup.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                  (@SetLike.instMembership.{u_1, u_1}
                    (@Subgroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@Subgroup.instSetLike.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
                  (@Subgroup.map.{u_1, u_1} G inst
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                    (@QuotientGroup.mk'.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                    H)
                  x)
              (@Monoid.toMulOneClass.{u_1}
                (@Subtype.{u_1 + 1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  fun
                    (x :
                      @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                  @Membership.mem.{u_1, u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@Subgroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                    (@SetLike.instMembership.{u_1, u_1}
                      (@Subgroup.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@Subgroup.instSetLike.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
                    (@Subgroup.map.{u_1, u_1} G inst
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                      (@QuotientGroup.mk'.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                      H)
                    x)
                (@DivInvMonoid.toMonoid.{u_1}
                  (@Subtype.{u_1 + 1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    fun
                      (x :
                        @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                    @Membership.mem.{u_1, u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@Subgroup.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                      (@SetLike.instMembership.{u_1, u_1}
                        (@Subgroup.{u_1}
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@Subgroup.instSetLike.{u_1}
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
                      (@Subgroup.map.{u_1, u_1} G inst
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                        (@QuotientGroup.mk'.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                        H)
                      x)
                  (@Group.toDivInvMonoid.{u_1}
                    (@Subtype.{u_1 + 1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      fun
                        (x :
                          @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                      @Membership.mem.{u_1, u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@Subgroup.{u_1}
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                        (@SetLike.instMembership.{u_1, u_1}
                          (@Subgroup.{u_1}
                            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                            (@QuotientGroup.Quotient.group.{u_1} G inst
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                              (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@Subgroup.instSetLike.{u_1}
                            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                            (@QuotientGroup.Quotient.group.{u_1} G inst
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                              (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
                        (@Subgroup.map.{u_1, u_1} G inst
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                          (@QuotientGroup.mk'.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                          H)
                        x)
                    (@Subgroup.toGroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                      (@Subgroup.map.{u_1, u_1} G inst
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                        (@QuotientGroup.mk'.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                        H))))))
            (@MulOneClass.toMulOne.{u_1}
              (@HasQuotient.Quotient.{u_1, u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H))
                (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H))
                (@OpenSubgroup.toSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H)
                  (@instTopologicalSpaceSubtype.{u_1} G
                    (fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    inst_1)
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H)
                    (@instTopologicalSpaceSubtype.{u_1} G
                      (fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      inst_1)
                    V)))
              (@Monoid.toMulOneClass.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H))
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H))
                  (@OpenSubgroup.toSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H)
                    (@instTopologicalSpaceSubtype.{u_1} G
                      (fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      inst_1)
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@instTopologicalSpaceSubtype.{u_1} G
                        (fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        inst_1)
                      V)))
                (@DivInvMonoid.toMonoid.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H))
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H))
                    (@OpenSubgroup.toSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@instTopologicalSpaceSubtype.{u_1} G
                        (fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        inst_1)
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        V)))
                  (@Group.toDivInvMonoid.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H))
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H))
                      (@OpenSubgroup.toSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                          (@Subtype.{u_1 + 1} G fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          (@Subgroup.toGroup.{u_1} G inst H)
                          (@instTopologicalSpaceSubtype.{u_1} G
                            (fun (x : G) =>
                              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                  (@Subgroup.instSetLike.{u_1} G inst))
                                H x)
                            inst_1)
                          V)))
                    (@QuotientGroup.Quotient.group.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@OpenSubgroup.toSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                          (@Subtype.{u_1 + 1} G fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          (@Subgroup.toGroup.{u_1} G inst H)
                          (@instTopologicalSpaceSubtype.{u_1} G
                            (fun (x : G) =>
                              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                  (@Subgroup.instSetLike.{u_1} G inst))
                                H x)
                            inst_1)
                          V))
                      (@OpenNormalSubgroup.instNormal.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        V)))))))
          (@Subtype.{u_1 + 1}
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
            fun
              (x :
                @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
            @Membership.mem.{u_1, u_1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@Subgroup.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@QuotientGroup.Quotient.group.{u_1} G inst
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
              (@SetLike.instMembership.{u_1, u_1}
                (@Subgroup.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@Subgroup.instSetLike.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
              (@Subgroup.map.{u_1, u_1} G inst
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@QuotientGroup.Quotient.group.{u_1} G inst
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                (@QuotientGroup.mk'.{u_1} G inst
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                  (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                H)
              x)
          (fun
              (x :
                @Subtype.{u_1 + 1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  fun
                    (x :
                      @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                  @Membership.mem.{u_1, u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@Subgroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                    (@SetLike.instMembership.{u_1, u_1}
                      (@Subgroup.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@Subgroup.instSetLike.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
                    (@Subgroup.map.{u_1, u_1} G inst
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                      (@QuotientGroup.mk'.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                      H)
                    x) =>
            @HasQuotient.Quotient.{u_1, u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              (@Subgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H))
              (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H))
              (@OpenSubgroup.toSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H)
                (@instTopologicalSpaceSubtype.{u_1} G
                  (fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  inst_1)
                (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H)
                  (@instTopologicalSpaceSubtype.{u_1} G
                    (fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    inst_1)
                  V)))
          (@MonoidHom.instFunLike.{u_1, u_1}
            (@Subtype.{u_1 + 1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              fun
                (x :
                  @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
              @Membership.mem.{u_1, u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                (@Subgroup.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                (@SetLike.instMembership.{u_1, u_1}
                  (@Subgroup.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@Subgroup.instSetLike.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
                (@Subgroup.map.{u_1, u_1} G inst
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                  (@QuotientGroup.mk'.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                  H)
                x)
            (@HasQuotient.Quotient.{u_1, u_1}
              (@Subtype.{u_1 + 1} G fun (x : G) =>
                @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) H
                  x)
              (@Subgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H))
              (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H))
              (@OpenSubgroup.toSubgroup.{u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.toGroup.{u_1} G inst H)
                (@instTopologicalSpaceSubtype.{u_1} G
                  (fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  inst_1)
                (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H)
                  (@instTopologicalSpaceSubtype.{u_1} G
                    (fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    inst_1)
                  V)))
            (@MulOneClass.toMulOne.{u_1}
              (@Subtype.{u_1 + 1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                fun
                  (x :
                    @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                @Membership.mem.{u_1, u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@Subgroup.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                  (@SetLike.instMembership.{u_1, u_1}
                    (@Subgroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@Subgroup.instSetLike.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
                  (@Subgroup.map.{u_1, u_1} G inst
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                    (@QuotientGroup.mk'.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                    H)
                  x)
              (@Monoid.toMulOneClass.{u_1}
                (@Subtype.{u_1 + 1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  fun
                    (x :
                      @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                  @Membership.mem.{u_1, u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@Subgroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                    (@SetLike.instMembership.{u_1, u_1}
                      (@Subgroup.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@Subgroup.instSetLike.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
                    (@Subgroup.map.{u_1, u_1} G inst
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                      (@QuotientGroup.mk'.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                      H)
                    x)
                (@DivInvMonoid.toMonoid.{u_1}
                  (@Subtype.{u_1 + 1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    fun
                      (x :
                        @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                    @Membership.mem.{u_1, u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@Subgroup.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                      (@SetLike.instMembership.{u_1, u_1}
                        (@Subgroup.{u_1}
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@Subgroup.instSetLike.{u_1}
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
                      (@Subgroup.map.{u_1, u_1} G inst
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                        (@QuotientGroup.mk'.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                        H)
                      x)
                  (@Group.toDivInvMonoid.{u_1}
                    (@Subtype.{u_1 + 1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      fun
                        (x :
                          @HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))) =>
                      @Membership.mem.{u_1, u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@Subgroup.{u_1}
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                        (@SetLike.instMembership.{u_1, u_1}
                          (@Subgroup.{u_1}
                            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                            (@QuotientGroup.Quotient.group.{u_1} G inst
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                              (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@Subgroup.instSetLike.{u_1}
                            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                            (@QuotientGroup.Quotient.group.{u_1} G inst
                              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                              (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))))
                        (@Subgroup.map.{u_1, u_1} G inst
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                          (@QuotientGroup.mk'.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                          H)
                        x)
                    (@Subgroup.toGroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                      (@Subgroup.map.{u_1, u_1} G inst
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                        (@QuotientGroup.mk'.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                        H))))))
            (@MulOneClass.toMulOne.{u_1}
              (@HasQuotient.Quotient.{u_1, u_1}
                (@Subtype.{u_1 + 1} G fun (x : G) =>
                  @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
                    H x)
                (@Subgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H))
                (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H))
                (@OpenSubgroup.toSubgroup.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.toGroup.{u_1} G inst H)
                  (@instTopologicalSpaceSubtype.{u_1} G
                    (fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    inst_1)
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H)
                    (@instTopologicalSpaceSubtype.{u_1} G
                      (fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      inst_1)
                    V)))
              (@Monoid.toMulOneClass.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      H x)
                  (@Subgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H))
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H))
                  (@OpenSubgroup.toSubgroup.{u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.toGroup.{u_1} G inst H)
                    (@instTopologicalSpaceSubtype.{u_1} G
                      (fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      inst_1)
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@instTopologicalSpaceSubtype.{u_1} G
                        (fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        inst_1)
                      V)))
                (@DivInvMonoid.toMonoid.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1}
                    (@Subtype.{u_1 + 1} G fun (x : G) =>
                      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                          (@Subgroup.instSetLike.{u_1} G inst))
                        H x)
                    (@Subgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H))
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H))
                    (@OpenSubgroup.toSubgroup.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@instTopologicalSpaceSubtype.{u_1} G
                        (fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        inst_1)
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        V)))
                  (@Group.toDivInvMonoid.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H))
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H))
                      (@OpenSubgroup.toSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                          (@Subtype.{u_1 + 1} G fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          (@Subgroup.toGroup.{u_1} G inst H)
                          (@instTopologicalSpaceSubtype.{u_1} G
                            (fun (x : G) =>
                              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                  (@Subgroup.instSetLike.{u_1} G inst))
                                H x)
                            inst_1)
                          V)))
                    (@QuotientGroup.Quotient.group.{u_1}
                      (@Subtype.{u_1 + 1} G fun (x : G) =>
                        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                            (@Subgroup.instSetLike.{u_1} G inst))
                          H x)
                      (@Subgroup.toGroup.{u_1} G inst H)
                      (@OpenSubgroup.toSubgroup.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1}
                          (@Subtype.{u_1 + 1} G fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          (@Subgroup.toGroup.{u_1} G inst H)
                          (@instTopologicalSpaceSubtype.{u_1} G
                            (fun (x : G) =>
                              @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                                (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                  (@Subgroup.instSetLike.{u_1} G inst))
                                H x)
                            inst_1)
                          V))
                      (@OpenNormalSubgroup.instNormal.{u_1}
                        (@Subtype.{u_1 + 1} G fun (x : G) =>
                          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                              (@Subgroup.instSetLike.{u_1} G inst))
                            H x)
                        (@Subgroup.toGroup.{u_1} G inst H)
                        (@instTopologicalSpaceSubtype.{u_1} G
                          (fun (x : G) =>
                            @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                                (@Subgroup.instSetLike.{u_1} G inst))
                              H x)
                          inst_1)
                        V)))))))
          f) := by sorry
