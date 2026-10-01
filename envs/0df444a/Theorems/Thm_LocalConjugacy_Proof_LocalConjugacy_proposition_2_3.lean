-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_proposition_2_3
-- name    : LocalConjugacy.Proof.LocalConjugacy.proposition_2_3
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:26:39.900049+00:00
-- url     : https://prove2.me/theorems/8ca4e330-0749-448d-b101-cc258e1605c8
-- title:
--   Bijective Hall restriction for primary coefficients
-- statement:
--   Let $J$ be a profinite group acting continuously by automorphisms on a finite discrete $p$-group $N$, where $p$ is prime. Suppose the semidirect product $N\rtimes J$ is prosupersolvable. Let $Q\le J$ be a closed Hall pro-subgroup for the primes at most $p$: its image in every finite continuous quotient is a Hall subgroup for that prime set. Then
--
--   $$
--   \operatorname{res}:H^1(J,N)\longrightarrow H^1(Q,N)
--   $$
--
--   is bijective, where $H^1$ is continuous nonabelian first cohomology.
--
--   This identifies all cohomology classes on the Hall subgroup with global classes, giving the Hall restriction conclusion used for primary coefficients.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/HallRestriction.lean, lines 57–85; source SHA-256 d558c26e22b95bd6f3429f38d8220889adf7c891cb672d196ccaaf4c2f430549.

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

theorem LocalConjugacy.Proof.LocalConjugacy.proposition_2_3 :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [inst_3 : TopologicalSpace.{u_2} N]
  [inst_4 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [@DiscreteTopology.{u_2} N inst_3]
  [Finite.{u_2 + 1} N]
  [@ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_4)))
      inst_2 inst_3]
  (p : Nat) (hp : Nat.Prime p) (hN : @IsPGroup.{u_2} p N inst_1)
  (hG :
    @LocalConjugacy.Proof.LocalConjugacy.Prosupersolvable.{max u_2 u_1}
      (@LocalConjugacy.Proof.LocalConjugacy.ActionProduct.{u_1, u_2} J N inst inst_1 inst_4)
      (@SemidirectProduct.instGroup.{u_2, u_1} N J inst_1 inst
        (@MulDistribMulAction.toMulAut.{u_1, u_2} J N inst
          (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_4))
      (@LocalConjugacy.Proof.LocalConjugacy.semidirectTopology.{u_1, u_2} J N inst inst_1 inst_2 inst_3
        (@MulDistribMulAction.toMulAut.{u_1, u_2} J N inst
          (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_4)))
  (Q : @Subgroup.{u_1} J inst)
  (hQ :
    @LocalConjugacy.Proof.LocalConjugacy.IsHallPro.{u_1} J inst inst_2
      (@Set.ofPred.{0} Nat fun (r : Nat) => @LE.le.{0} Nat instLENat r p) Q),
  @Function.Bijective.{max (u_2 + 1) (u_1 + 1), max (u_2 + 1) (u_1 + 1)}
    (@LocalConjugacy.Proof.LocalConjugacy.H1.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)))
    (@LocalConjugacy.Proof.LocalConjugacy.H1.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4 Q)
    (@LocalConjugacy.Proof.LocalConjugacy.restrictH1.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4 Q
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst))
      (have this :
        @LE.le.{u_1} (@Subgroup.{u_1} J inst)
          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
          Q (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) :=
        @le_top.{u_1} (@Subgroup.{u_1} J inst)
          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
          (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
              (@Subgroup.instCompleteLattice.{u_1} J inst)))
          Q;
      this)) := by sorry
