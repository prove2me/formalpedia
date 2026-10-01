-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_sylowPro_normal_of_prosupersolvable_largest
-- name    : LocalConjugacy.Proof.LocalConjugacy.sylowPro_normal_of_prosupersolvable_largest
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:15:19.563076+00:00
-- url     : https://prove2.me/theorems/7fb27af7-97b1-4209-bd74-59ee93a40b58
-- title:
--   Normality of largest-prime Sylow subgroups
-- statement:
--   Let $G$ be a prosupersolvable profinite group and let $p$ be prime. Assume that for every open normal subgroup $U\trianglelefteq G$, every prime divisor of $|G/U|$ is at most $p$. If $P$ is a Sylow pro-$p$ subgroup of $G$, then
--
--   $$P\trianglelefteq G.$$
--
--   This extends the largest-prime normal Sylow property to profinite groups through their finite quotients.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/SupersolvableReductions.lean, lines 136–152; source SHA-256 29509bd9dc03344a0acef30e2bd052c64781f5f1093f7c226e23a6aa0ad6969d.

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

theorem LocalConjugacy.Proof.LocalConjugacy.sylowPro_normal_of_prosupersolvable_largest :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1]
  (hG : @LocalConjugacy.Proof.LocalConjugacy.Prosupersolvable.{u_1} G inst inst_1) {p : Nat} [Fact (Nat.Prime p)]
  (hprimes :
    ∀ (U : @OpenNormalSubgroup.{u_1} G inst inst_1),
      @LocalConjugacy.Proof.LocalConjugacy.HasPrimes.{u_1}
        (@Set.ofPred.{0} Nat fun (r : Nat) => @LE.le.{0} Nat instLENat r p)
        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
        (@QuotientGroup.Quotient.group.{u_1} G inst
          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
  (P : @Subgroup.{u_1} G inst)
  (hP :
    @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1} p G inst inst_1
      (@Top.top.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instTop.{u_1} G inst)) P),
  @Subgroup.Normal.{u_1} G inst P := by sorry
