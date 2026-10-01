-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_primaryDecomposition_pGroup_of_restriction
-- name    : LocalConjugacy.Proof.LocalConjugacy.primaryDecomposition_pGroup_of_restriction
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:05:53.579568+00:00
-- url     : https://prove2.me/theorems/6c74c01d-c8a5-4487-b13d-f0e3eb85e1ca
-- title:
--   Primary decomposition from the Sylow restriction theorem
-- statement:
--   Let $J$ be a profinite group acting continuously by automorphisms on a finite discrete $p$-group $N$, where $p$ is prime. Assume that for every Sylow pro-$p$ subgroup $Q\le J$, restriction is injective on $H^1(J,N)$ and every $J$-stable class on $Q$ is its restriction. Let $\pi(J)$ be the primes dividing the order of at least one finite continuous quotient of $J$, and choose a Sylow pro-$q$ subgroup $P_q$ for each $q\in\pi(J)$. Then
--
--   $$
--   \operatorname{res}:H^1(J,N)\longrightarrow
--   \prod_{q\in\pi(J)}H^1(P_q,N)^{\mathrm{st}}
--   $$
--
--   is well-defined and bijective.
--
--   Here $H^1$ denotes continuous nonabelian first cohomology. A class on a subgroup $L\le J$ is $J$-stable if a representative $c$ satisfies: for every $j\in J$ there is $n_j\in N$ such that $j\cdot c(j^{-1}xj)=n_j^{-1}c(x)(x\cdot n_j)$ for all $x\in L\cap jLj^{-1}$. The superscript $\mathrm{st}$ denotes these stable classes.
--
--   This assembles primary decomposition for $p$-group coefficients from restriction to Sylow pro-$p$ subgroups.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/PrimaryPGroup.lean, lines 24–64; source SHA-256 a967a745bc1c01a56144136b4bc1f6b05b5f28b7660e808b28e1af357aa35f90.

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

theorem LocalConjugacy.Proof.LocalConjugacy.primaryDecomposition_pGroup_of_restriction :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@DiscreteTopology.{u_2} N inst_4] [Finite.{u_2 + 1} N]
  [inst_7 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [@ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_7)))
      inst_2 inst_4]
  {p : Nat} [Fact (Nat.Prime p)] (hN : @IsPGroup.{u_2} p N inst_1)
  (hres :
    ∀ (Q : @Subgroup.{u_1} J inst),
      @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1} p J inst inst_2
          (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) Q →
        @LocalConjugacy.Proof.LocalConjugacy.RestrictionIsomorphism.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7
          (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) Q
          (@le_top.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
              (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
              (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                (@Subgroup.instCompleteLattice.{u_1} J inst)))
            Q))
  (P : @LocalConjugacy.Proof.LocalConjugacy.PrimeDivisor.{u_1} J inst inst_2 → @Subgroup.{u_1} J inst)
  (hP :
    ∀ (q : @LocalConjugacy.Proof.LocalConjugacy.PrimeDivisor.{u_1} J inst inst_2),
      @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1}
        (@Subtype.val.{1} Nat (fun (p : Nat) => Nat.Prime p)
          (@Subtype.val.{1} Nat.Primes
            (fun (p : Nat.Primes) =>
              @Exists.{u_1 + 1} (@OpenNormalSubgroup.{u_1} J inst inst_2)
                fun (U : @OpenNormalSubgroup.{u_1} J inst inst_2) =>
                @Dvd.dvd.{0} Nat Nat.instDvd (@Subtype.val.{1} Nat (fun (p : Nat) => Nat.Prime p) p)
                  (Nat.card.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} J inst)
                      (@OpenSubgroup.toSubgroup.{u_1} J inst inst_2
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} J inst inst_2 U)))))
            q))
        J inst inst_2 (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) (P q)),
  @LocalConjugacy.Proof.LocalConjugacy.PrimaryDecomposition.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 P := by sorry
