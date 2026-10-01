-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_supersolvable_hall_split_containing
-- name    : LocalConjugacy.Proof.LocalConjugacy.supersolvable_hall_split_containing
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:51:24.190827+00:00
-- url     : https://prove2.me/theorems/0ea97ecb-aa01-446f-ac5d-e5c69c51f4ec
-- title:
--   A Hall complement containing a prescribed Sylow subgroup
-- statement:
--   Let $G$ be a finite supersolvable group, $n\in\mathbb N$, and $p\le n$ a prime. Let $P$ be a Sylow $p$-subgroup of $G$, and let $M\trianglelefteq G$ be a Hall subgroup for the primes greater than $n$: all prime divisors of $|M|$ exceed $n$, and all prime divisors of $[G:M]$ are at most $n$. Then there is a subgroup $Q\le G$ such that
--
--   $$
--   G=MQ,\qquad M\cap Q=1,\qquad P\le Q,
--   $$
--
--   and $Q$ is a Hall subgroup for the primes at most $n$.
--
--   This refines the Hall decomposition by keeping a chosen Sylow subgroup inside the complementary factor.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/SupersolvableStructure.lean, lines 211–229; source SHA-256 c06f9eac035d521faa11c587697ded75f3b001382a70b83938592f249f234b48.

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

theorem LocalConjugacy.Proof.LocalConjugacy.supersolvable_hall_split_containing :
∀ {G : Type u_1} [inst : Group.{u_1} G] [Finite.{u_1 + 1} G]
  (hG : @LocalConjugacy.Proof.LocalConjugacy.Supersolvable.{u_1} G inst) {n p : Nat} [Fact (Nat.Prime p)]
  (hpn : @LE.le.{0} Nat instLENat p n) (P : @Sylow.{u_1} p G inst) (M : @Subgroup.{u_1} G inst)
  [@Subgroup.Normal.{u_1} G inst M]
  (hM :
    @LocalConjugacy.Proof.LocalConjugacy.IsHall.{u_1} G inst
      (@Set.ofPred.{0} Nat fun (r : Nat) => @LT.lt.{0} Nat instLTNat n r) M),
  @Exists.{u_1 + 1} (@Subgroup.{u_1} G inst) fun (Q : @Subgroup.{u_1} G inst) =>
    And (@Subgroup.IsComplement'.{u_1} G inst M Q)
      (And
        (@LocalConjugacy.Proof.LocalConjugacy.IsHall.{u_1} G inst
          (@Set.ofPred.{0} Nat fun (r : Nat) => @LE.le.{0} Nat instLENat r n) Q)
        (@LE.le.{u_1} (@Subgroup.{u_1} G inst)
          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
          (@Sylow.toSubgroup.{u_1} p G inst P) Q)) := by sorry
