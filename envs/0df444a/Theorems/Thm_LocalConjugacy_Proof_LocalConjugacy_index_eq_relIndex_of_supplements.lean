-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_index_eq_relIndex_of_supplements
-- name    : LocalConjugacy.Proof.LocalConjugacy.index_eq_relIndex_of_supplements
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:24:01.462664+00:00
-- url     : https://prove2.me/theorems/9aca06da-9bb2-4e3f-b271-07033ac53b00
-- title:
--   Index of a supplement through its normal-factor intersection
-- statement:
--   Let $G$ be finite, let $N\trianglelefteq G$, and let $H\le G$ satisfy $G=NH$. Then
--
--   $$[G:H]=[N:N\cap H].$$
--
--   This identifies the index of a supplement with its relative index inside the normal factor, allowing ambient index calculations to be reduced to $N$.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/FiniteConjugacyTools.lean, lines 120–135; source SHA-256 66a390bc8fe558b2bcb53068e36dde3733d5ed0919c371d0dc06e77931123d28.

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

theorem LocalConjugacy.Proof.LocalConjugacy.index_eq_relIndex_of_supplements :
∀ {G : Type u_1} [inst : Group.{u_1} G] [Finite.{u_1 + 1} G] (N H : @Subgroup.{u_1} G inst)
  [@Subgroup.Normal.{u_1} G inst N] (hs : @LocalConjugacy.Proof.LocalConjugacy.Supplements.{u_1} G inst N H),
  @Eq.{1} Nat (@Subgroup.index.{u_1} G inst H) (@Subgroup.relIndex.{u_1} G inst H N) := by sorry
