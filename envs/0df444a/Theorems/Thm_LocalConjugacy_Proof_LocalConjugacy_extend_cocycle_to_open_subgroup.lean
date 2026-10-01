-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_extend_cocycle_to_open_subgroup
-- name    : LocalConjugacy.Proof.LocalConjugacy.extend_cocycle_to_open_subgroup
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:03:26.600861+00:00
-- url     : https://prove2.me/theorems/8f37d66c-191b-4ea2-9702-6acd76c49ddb
-- title:
--   A cocycle extends to an open subgroup
-- statement:
--   Let $J$ be a profinite group acting continuously by automorphisms on a discrete group $N$. Let $H\le J$ be a closed subgroup and $f:H\to N$ a continuous cocycle. Then
--
--   $$
--   \exists V\le J\text{ open},\quad H\le V,\quad
--   \exists F\in Z^1_{\mathrm{cts}}(V,N),\quad F|_H=f.
--   $$
--
--   Here $Z^1_{\mathrm{cts}}(V,N)$ consists of continuous maps satisfying $F(xy)=F(x)(x\cdot F(y))$. This allows cocycles on closed subgroups to be studied first on open overgroups.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/CocycleNeighborhood.lean, lines 46–114; source SHA-256 d708cc0d5984b02fa63014c3330a19c97523def77ef9336dec26550725e897b0.

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

universe u_1 u_2

theorem LocalConjugacy.Proof.LocalConjugacy.extend_cocycle_to_open_subgroup :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@DiscreteTopology.{u_2} N inst_4]
  [inst_6 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [@ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_6)))
      inst_2 inst_4]
  (H : @Subgroup.{u_1} J inst)
  (hH :
    @IsClosed.{u_1} J inst_2
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) H))
  (f : @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 H),
  @Exists.{u_1 + 1} (@Subgroup.{u_1} J inst) fun (V : @Subgroup.{u_1} J inst) =>
    @Exists.{0}
      (@LE.le.{u_1} (@Subgroup.{u_1} J inst)
        (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
          (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
        H V)
      fun
        (hHV :
          @LE.le.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            H V) =>
      And
        (@IsOpen.{u_1} J inst_2
          (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) V))
        (@Exists.{max (u_1 + 1) (u_2 + 1)}
          (@LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 V)
          fun (F : @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 V) =>
          @Eq.{max (u_1 + 1) (u_2 + 1)}
            (@LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 H)
            (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 H V
              hHV F)
            f) := by sorry
