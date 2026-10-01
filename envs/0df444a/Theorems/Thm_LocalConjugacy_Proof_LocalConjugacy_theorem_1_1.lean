-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_theorem_1_1
-- name    : LocalConjugacy.Proof.LocalConjugacy.theorem_1_1
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:25:40.000325+00:00
-- url     : https://prove2.me/theorems/b1544097-3473-4ce7-92d5-8f54bf64f4e7
-- title:
--   Local conjugacy of pronilpotent supplements
-- statement:
--   Let $G$ be profinite, let $N\trianglelefteq G$ be closed and pronilpotent, and let $H,K\le G$ be closed subgroups satisfying $G=NH=NK$. Assume either that $G$ is prosupersolvable or that $G/N$ is pronilpotent. Then
--
--   $$H\text{ and }K\text{ are conjugate in }G\quad\Longleftrightarrow\quad H\text{ and }K\text{ are locally conjugate in }G.$$
--
--   Here local conjugacy means that for every prime $p$, a Sylow pro-$p$ subgroup of $H$ and a Sylow pro-$p$ subgroup of $K$ are conjugate in $G$. No trivial-intersection condition on $N\cap H$ or $N\cap K$ is imposed.
--
--   This is the project's local-to-global conjugacy theorem for supplements of a pronilpotent normal subgroup.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/NormalIntersectionCompactness.lean, lines 84–108; source SHA-256 68b5478cd18e7a5843a6fdb9d6f7769e11034c75d256076dc80570e53a4f583e.

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

theorem LocalConjugacy.Proof.LocalConjugacy.theorem_1_1 :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1] (N H K : @Subgroup.{u_1} G inst)
  [inst_3 : @Subgroup.Normal.{u_1} G inst N]
  (hN :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) N))
  (hH :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) H))
  (hK :
    @IsClosed.{u_1} G inst_1
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) K))
  (hpron :
    @LocalConjugacy.Proof.LocalConjugacy.Pronilpotent.{u_1}
      (@Subtype.{u_1 + 1} G fun (x : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
      (@Subgroup.toGroup.{u_1} G inst N)
      (@instTopologicalSpaceSubtype.{u_1} G
        (fun (x : G) =>
          @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) N x)
        inst_1))
  (hcase :
    Or (@LocalConjugacy.Proof.LocalConjugacy.Prosupersolvable.{u_1} G inst inst_1)
      (@LocalConjugacy.Proof.LocalConjugacy.Pronilpotent.{u_1}
        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst) N)
        (@QuotientGroup.Quotient.group.{u_1} G inst N inst_3)
        (@QuotientGroup.instTopologicalSpace.{u_1} G inst_1 inst N)))
  (hHN : @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N H)
  (hKN : @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N K),
  Iff (@LocalConjugacy.Proof.LocalConjugacy.Conjugate.{u_1} G inst H K)
    (@LocalConjugacy.Proof.LocalConjugacy.LocallyConjugate.{u_1} G inst inst_1 H K) := by sorry
