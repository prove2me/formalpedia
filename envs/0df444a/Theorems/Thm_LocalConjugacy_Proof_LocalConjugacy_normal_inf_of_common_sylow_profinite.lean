-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_normal_inf_of_common_sylow_profinite
-- name    : LocalConjugacy.Proof.LocalConjugacy.normal_inf_of_common_sylow_profinite
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:26:52.393932+00:00
-- url     : https://prove2.me/theorems/b434991d-5403-423e-b22e-e9f5d1bf5926
-- title:
--   A common Sylow forces a normal common kernel intersection
-- statement:
--   Let $G$ be a profinite group, let $p$ be prime, and let $N\trianglelefteq G$ be an algebraic $p$-group, meaning every element has order a power of $p$. Let $H,K\le G$ be closed subgroups generating $G$ as a group. Suppose $P\le G$ is simultaneously a Sylow pro-$p$ subgroup of $H$ and of $K$. Then
--
--   $$
--   N\cap H=N\cap K,\qquad N\cap H\trianglelefteq G.
--   $$
--
--   This produces a common normal intersection for quotient reductions after the relevant Sylow subgroups have been aligned.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/FiniteKernelSylow.lean, lines 30–48; source SHA-256 4cc6aa4c9f883bff52303e9074afbc77e4bc971fe7011f4acd9a1dbc91af24b7.

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

theorem LocalConjugacy.Proof.LocalConjugacy.normal_inf_of_common_sylow_profinite :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1] (N H K P : @Subgroup.{u_1} G inst)
  [@Subgroup.Normal.{u_1} G inst N]
  (hH :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) H))
  (hK :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) K))
  {p : Nat} [Fact (Nat.Prime p)]
  (hN :
    @IsPGroup.{u_1} p
      (@Subtype.{u_1 + 1} G fun (x : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
      (@Subgroup.toGroup.{u_1} G inst N))
  (hPH : @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1} p G inst inst_1 H P)
  (hPK : @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1} p G inst inst_1 K P)
  (hgen :
    @Eq.{u_1 + 1} (@Subgroup.{u_1} G inst)
      (@Max.max.{u_1} (@Subgroup.{u_1} G inst)
        (@SemilatticeSup.toMax.{u_1} (@Subgroup.{u_1} G inst)
          (@Lattice.toSemilatticeSup.{u_1} (@Subgroup.{u_1} G inst)
            (@ConditionallyCompleteLattice.toLattice.{u_1} (@Subgroup.{u_1} G inst)
              (@CompleteLattice.toConditionallyCompleteLattice.{u_1} (@Subgroup.{u_1} G inst)
                (@Subgroup.instCompleteLattice.{u_1} G inst)))))
        H K)
      (@Top.top.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instTop.{u_1} G inst))),
  And
    (@Eq.{u_1 + 1} (@Subgroup.{u_1} G inst)
      (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N H)
      (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N K))
    (@Subgroup.Normal.{u_1} G inst (@Min.min.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instMin.{u_1} G inst) N H)) := by sorry
