-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_cutoff_hall_isComplement
-- name    : LocalConjugacy.Proof.LocalConjugacy.cutoff_hall_isComplement
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:59:06.40725+00:00
-- url     : https://prove2.me/theorems/f19d5a1b-6f8c-49b8-bc8a-419794cb29b1
-- title:
--   Complementary Hall cutoffs split a profinite group
-- statement:
--   Let $J$ be a profinite group and $p\in\mathbb N$. Let $M\trianglelefteq J$ and $Q\le J$ be closed subgroups. Suppose that in every finite continuous quotient of $J$, the image of $M$ is a Hall subgroup for primes greater than $p$, and the image of $Q$ is a Hall subgroup for primes at most $p$. Then
--
--   $$
--   J=MQ,\qquad M\cap Q=1.
--   $$
--
--   A Hall subgroup for a set of primes has order supported on that set and index supported on its complement. This supplies the complement condition for the two sides of a profinite Hall cutoff.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/HallRestriction.lean, lines 18–51; source SHA-256 d558c26e22b95bd6f3429f38d8220889adf7c891cb672d196ccaaf4c2f430549.

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

theorem LocalConjugacy.Proof.LocalConjugacy.cutoff_hall_isComplement :
∀ {J : Type u_1} [inst : Group.{u_1} J] [inst_1 : TopologicalSpace.{u_1} J]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_1] {p : Nat} (M Q : @Subgroup.{u_1} J inst)
  [@Subgroup.Normal.{u_1} J inst M]
  (hM :
    @LocalConjugacy.Proof.LocalConjugacy.IsHallPro.{u_1} J inst inst_1
      (@Set.ofPred.{0} Nat fun (r : Nat) => @LT.lt.{0} Nat instLTNat p r) M)
  (hQ :
    @LocalConjugacy.Proof.LocalConjugacy.IsHallPro.{u_1} J inst inst_1
      (@Set.ofPred.{0} Nat fun (r : Nat) => @LE.le.{0} Nat instLENat r p) Q),
  @Subgroup.IsComplement'.{u_1} J inst M Q := by sorry
