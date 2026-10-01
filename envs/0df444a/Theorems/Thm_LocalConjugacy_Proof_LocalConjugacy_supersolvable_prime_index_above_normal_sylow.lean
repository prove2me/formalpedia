-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_supersolvable_prime_index_above_normal_sylow
-- name    : LocalConjugacy.Proof.LocalConjugacy.supersolvable_prime_index_above_normal_sylow
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:14:08.688779+00:00
-- url     : https://prove2.me/theorems/fd24528d-77d9-41c8-bc29-646cfe15adf2
-- title:
--   A prime-index overgroup of a proper normal Sylow subgroup
-- statement:
--   Let $G$ be a finite supersolvable group, let $p$ be prime, and let $P\trianglelefteq G$ be a Sylow $p$-subgroup with $P\ne G$. Then
--
--   $$\exists K\trianglelefteq G,\qquad P\le K,\quad [G:K]\text{ is prime},\quad [G:K]\ne p.$$
--
--   This supplies a normal subgroup of a different prime index above a proper normal Sylow subgroup.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/SupersolvableReductions.lean, lines 83–101; source SHA-256 29509bd9dc03344a0acef30e2bd052c64781f5f1093f7c226e23a6aa0ad6969d.

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

theorem LocalConjugacy.Proof.LocalConjugacy.supersolvable_prime_index_above_normal_sylow :
∀ {G : Type u_1} [inst : Group.{u_1} G] [Finite.{u_1 + 1} G]
  (hG : @LocalConjugacy.Proof.LocalConjugacy.Supersolvable.{u_1} G inst) {p : Nat} [Fact (Nat.Prime p)]
  (P : @Sylow.{u_1} p G inst) [@Subgroup.Normal.{u_1} G inst (@Sylow.toSubgroup.{u_1} p G inst P)]
  (hP :
    @Ne.{u_1 + 1} (@Subgroup.{u_1} G inst) (@Sylow.toSubgroup.{u_1} p G inst P)
      (@Top.top.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instTop.{u_1} G inst))),
  @Exists.{u_1 + 1} (@Subgroup.{u_1} G inst) fun (K : @Subgroup.{u_1} G inst) =>
    And (@Subgroup.Normal.{u_1} G inst K)
      (And
        (@LE.le.{u_1} (@Subgroup.{u_1} G inst)
          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
          (@Sylow.toSubgroup.{u_1} p G inst P) K)
        (And (Nat.Prime (@Subgroup.index.{u_1} G inst K)) (@Ne.{1} Nat (@Subgroup.index.{u_1} G inst K) p))) := by sorry
