-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_supersolvable_exists_prime_index
-- name    : LocalConjugacy.Proof.LocalConjugacy.supersolvable_exists_prime_index
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:13:20.409657+00:00
-- url     : https://prove2.me/theorems/a7a42c70-754c-43ee-8062-39756b22955d
-- title:
--   A normal subgroup of prime index in a supersolvable group
-- statement:
--   Let $G$ be a nontrivial finite supersolvable group. Then
--
--   $$\exists K\trianglelefteq G,\qquad [G:K]\text{ is prime}.$$
--
--   Supersolvability means that $G$ admits a finite series of subgroups normal in $G$ with cyclic factors. The result supplies a prime-index normal reduction for induction and restriction arguments.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/SupersolvableReductions.lean, lines 52–81; source SHA-256 29509bd9dc03344a0acef30e2bd052c64781f5f1093f7c226e23a6aa0ad6969d.

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

theorem LocalConjugacy.Proof.LocalConjugacy.supersolvable_exists_prime_index :
∀ {G : Type u} [inst : Group.{u} G] [Finite.{u + 1} G] [Nontrivial.{u} G]
  (hG : @LocalConjugacy.Proof.LocalConjugacy.Supersolvable.{u} G inst),
  @Exists.{u + 1} (@Subgroup.{u} G inst) fun (K : @Subgroup.{u} G inst) =>
    And (@Subgroup.Normal.{u} G inst K) (Nat.Prime (@Subgroup.index.{u} G inst K)) := by sorry
