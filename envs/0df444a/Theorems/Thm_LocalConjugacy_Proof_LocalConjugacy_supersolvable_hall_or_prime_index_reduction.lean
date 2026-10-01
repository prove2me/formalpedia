-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_supersolvable_hall_or_prime_index_reduction
-- name    : LocalConjugacy.Proof.LocalConjugacy.supersolvable_hall_or_prime_index_reduction
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:15:24.525415+00:00
-- url     : https://prove2.me/theorems/db50a36e-6c42-4f40-9d22-5cfb23b93069
-- title:
--   Hall or prime-index reduction for primary cohomology
-- statement:
--   Let $J$ be a profinite group acting continuously by automorphisms on a finite discrete $p$-group $N$, where $p$ is prime. Assume $N\rtimes J$ is prosupersolvable, and let $P\le J$ be a proper Sylow pro-$p$ subgroup. Then at least one of the following holds.
--
--   1. There are closed Hall pro-subgroups $M,Q\le J$, for primes greater than $p$ and at most $p$, respectively, such that
--
--   $$
--   M\trianglelefteq J,\quad J=MQ,\quad M\cap Q=1,\quad P\le Q<J,
--   $$
--
--   and restriction is injective on $H^1(J,N)$ and surjective onto $H^1(Q,N)^{\mathrm{st}}$.
--
--   2. The subgroup $P$ is normal in $J$, and
--
--   $$
--   \exists K\trianglelefteq_{\mathrm{open}}J,\qquad P\le K,\quad [J:K]\text{ prime},\quad [J:K]\ne p.
--   $$
--
--   A Hall pro-subgroup is closed and has a Hall image for the indicated prime set in every finite continuous quotient.
--
--   Here $H^1$ denotes continuous nonabelian first cohomology. A class on a subgroup $L\le J$ is $J$-stable if a representative $c$ satisfies: for every $j\in J$ there is $n_j\in N$ such that $j\cdot c(j^{-1}xj)=n_j^{-1}c(x)(x\cdot n_j)$ for all $x\in L\cap jLj^{-1}$. The superscript $\mathrm{st}$ denotes these stable classes.
--
--   This supplies the two structural alternatives used to reduce the Sylow restriction problem to a proper overgroup.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/SupersolvableHallAction.lean, lines 60–86; source SHA-256 9aeea418a6f8cfeb20782ae1262d34959f06fddf55616fbc4655875bffc04ad9.

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

theorem LocalConjugacy.Proof.LocalConjugacy.supersolvable_hall_or_prime_index_reduction :
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
  (hG :
    @LocalConjugacy.Proof.LocalConjugacy.Prosupersolvable.{max u_2 u_1}
      (@LocalConjugacy.Proof.LocalConjugacy.ActionProduct.{u_1, u_2} J N inst inst_1 inst_7)
      (@SemidirectProduct.instGroup.{u_2, u_1} N J inst_1 inst
        (@MulDistribMulAction.toMulAut.{u_1, u_2} J N inst
          (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_7))
      (@LocalConjugacy.Proof.LocalConjugacy.semidirectTopology.{u_1, u_2} J N inst inst_1 inst_2 inst_4
        (@MulDistribMulAction.toMulAut.{u_1, u_2} J N inst
          (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_7)))
  {p : Nat} [Fact (Nat.Prime p)] (hN : @IsPGroup.{u_2} p N inst_1) (P : @Subgroup.{u_1} J inst)
  (hP :
    @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1} p J inst inst_2
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) P)
  (hproper :
    @Ne.{u_1 + 1} (@Subgroup.{u_1} J inst) P
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst))),
  Or
    (@Exists.{u_1 + 1} (@Subgroup.{u_1} J inst) fun (M : @Subgroup.{u_1} J inst) =>
      @Exists.{u_1 + 1} (@Subgroup.{u_1} J inst) fun (Q : @Subgroup.{u_1} J inst) =>
        And (@Subgroup.Normal.{u_1} J inst M)
          (And
            (@LocalConjugacy.Proof.LocalConjugacy.IsHallPro.{u_1} J inst inst_2
              (@Set.ofPred.{0} Nat fun (r : Nat) => @LT.lt.{0} Nat instLTNat p r) M)
            (And
              (@LocalConjugacy.Proof.LocalConjugacy.IsHallPro.{u_1} J inst inst_2
                (@Set.ofPred.{0} Nat fun (r : Nat) => @LE.le.{0} Nat instLENat r p) Q)
              (And (@Subgroup.IsComplement'.{u_1} J inst M Q)
                (And
                  (@LE.le.{u_1} (@Subgroup.{u_1} J inst)
                    (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                      (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                        (@Subgroup.instPartialOrder.{u_1} J inst)))
                    P Q)
                  (And
                    (@LT.lt.{u_1} (@Subgroup.{u_1} J inst)
                      (@Preorder.toLT.{u_1} (@Subgroup.{u_1} J inst)
                        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                          (@Subgroup.instPartialOrder.{u_1} J inst)))
                      Q (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)))
                    (@LocalConjugacy.Proof.LocalConjugacy.RestrictionIsomorphism.{u_1, u_2} J N inst inst_1 inst_2
                      inst_4 inst_7 (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) Q
                      (@le_top.{u_1} (@Subgroup.{u_1} J inst)
                        (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                          (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                            (@Subgroup.instPartialOrder.{u_1} J inst)))
                        (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
                          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                              (@Subgroup.instPartialOrder.{u_1} J inst)))
                          (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                            (@Subgroup.instCompleteLattice.{u_1} J inst)))
                        Q))))))))
    (And (@Subgroup.Normal.{u_1} J inst P)
      (@Exists.{u_1 + 1} (@OpenNormalSubgroup.{u_1} J inst inst_2) fun (K : @OpenNormalSubgroup.{u_1} J inst inst_2) =>
        And
          (@LE.le.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            P (@OpenSubgroup.toSubgroup.{u_1} J inst inst_2 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} J inst inst_2 K)))
          (And
            (Nat.Prime
              (@Subgroup.index.{u_1} J inst
                (@OpenSubgroup.toSubgroup.{u_1} J inst inst_2
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} J inst inst_2 K))))
            (@Ne.{1} Nat
              (@Subgroup.index.{u_1} J inst
                (@OpenSubgroup.toSubgroup.{u_1} J inst inst_2
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} J inst inst_2 K)))
              p)))) := by sorry
