-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_nilpotent_coatom_prime_index
-- name    : LocalConjugacy.Proof.LocalConjugacy.nilpotent_coatom_prime_index
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:06:58.031117+00:00
-- url     : https://prove2.me/theorems/a2cfadee-2e5f-4ad3-91d3-7f369eb275d5
-- title:
--   Maximal subgroups of finite nilpotent groups
-- statement:
--   Let $J$ be a finite nilpotent group and let $K<J$ be a maximal proper subgroup. Then
--
--   $$K\trianglelefteq J,\qquad [J:K]\text{ is prime}.$$
--
--   This supplies the normal prime-index step used in induction on finite nilpotent acting groups.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/NilpotentRestriction.lean, lines 11–34; source SHA-256 5e43828ef55fd3ce4909517da202bece972458138f2d1ed1af24d3ce01ad59fb.

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

theorem LocalConjugacy.Proof.LocalConjugacy.nilpotent_coatom_prime_index :
∀ {J : Type u_1} [inst : Group.{u_1} J] [Finite.{u_1 + 1} J] [@Group.IsNilpotent.{u_1} J inst]
  (K : @Subgroup.{u_1} J inst)
  (hK :
    @IsCoatom.{u_1} (@Subgroup.{u_1} J inst)
      (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst))
      (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
        (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
          (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
        (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instCompleteLattice.{u_1} J inst)))
      K),
  And (@Subgroup.Normal.{u_1} J inst K) (Nat.Prime (@Subgroup.index.{u_1} J inst K)) := by sorry
