-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_finite_supplements_of_locallyContains
-- name    : LocalConjugacy.Proof.LocalConjugacy.finite_supplements_of_locallyContains
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:18:38.841755+00:00
-- url     : https://prove2.me/theorems/63645f06-851e-4052-bea5-53f6126c36bb
-- title:
--   Local containment preserves supplements in finite groups
-- statement:
--   Let $G$ be a finite group with the discrete topology, let $N\trianglelefteq G$, and let $H,J\le G$. Suppose $G=NJ$, and suppose that for every prime $p$, the subgroup $H$ contains a $G$-conjugate of some Sylow $p$-subgroup of $J$. Then
--
--   $$
--   G=NH.
--   $$
--
--   The products here are setwise products of subgroups. This transfers the supplement property from $J$ to a subgroup locally containing it.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/LocalSupplement.lean, lines 26–47; source SHA-256 f1034a8ac923c57c992bf6e1e92c87e4819827b792e33ad753c4d18508d1c398.

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

theorem LocalConjugacy.Proof.LocalConjugacy.finite_supplements_of_locallyContains :
∀ {G : Type u_1} [inst : Group.{u_1} G] [Finite.{u_1 + 1} G] [inst_2 : TopologicalSpace.{u_1} G]
  [@DiscreteTopology.{u_1} G inst_2] (N H J : @Subgroup.{u_1} G inst) [@Subgroup.Normal.{u_1} G inst N]
  (hNJ : @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N J)
  (hloc : @LocalConjugacy.Proof.LocalConjugacy.LocallyContains.{u_1} G inst inst_2 H J),
  @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N H := by sorry
