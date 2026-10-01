-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_hasPrimes_singleton_iff_isPGroup
-- name    : LocalConjugacy.Proof.LocalConjugacy.hasPrimes_singleton_iff_isPGroup
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:10:01.953867+00:00
-- url     : https://prove2.me/theorems/e847e844-6734-4b23-a13d-73674e0f49d7
-- title:
--   A single allowed prime characterizes finite p-groups
-- statement:
--   Let $G$ be a finite group and let $p$ be prime. Then
--
--   $$\bigl(\forall r\text{ prime},\ r\mid|G|\Longrightarrow r=p\bigr)\quad\Longleftrightarrow\quad G\text{ is a }p\text{-group}.$$
--
--   A $p$-group means that every element has order a power of $p$; for finite groups this is equivalent to $|G|$ being a power of $p$. This translates the allowed-prime predicate into the usual Sylow-theoretic condition, including the trivial group.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/SupersolvableReductions.lean, lines 12–25; source SHA-256 29509bd9dc03344a0acef30e2bd052c64781f5f1093f7c226e23a6aa0ad6969d.

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

theorem LocalConjugacy.Proof.LocalConjugacy.hasPrimes_singleton_iff_isPGroup :
∀ {G : Type u_1} [inst : Group.{u_1} G] [Finite.{u_1 + 1} G] {p : Nat} [hp : Fact (Nat.Prime p)],
  Iff
    (@LocalConjugacy.Proof.LocalConjugacy.HasPrimes.{u_1}
      (@Singleton.singleton.{0, 0} Nat (Set.{0} Nat) (@Set.instSingletonSet.{0} Nat) p) G inst)
    (@IsPGroup.{u_1} p G inst) := by sorry
