-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_lemma_1_2_of_prosupersolvable
-- name    : LocalConjugacy.Proof.LocalConjugacy.lemma_1_2_of_prosupersolvable
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:16:11.55425+00:00
-- url     : https://prove2.me/theorems/6751f2c6-cd59-4665-af90-91770f691ec0
-- title:
--   Primary decomposition for prosupersolvable semidirect products
-- statement:
--   Let $J$ be a profinite group acting continuously by automorphisms on a finite discrete pronilpotent group $N$. Suppose the semidirect product $N\rtimes J$ is prosupersolvable. Let $\pi(J)$ be the primes dividing the order of at least one finite continuous quotient of $J$, and choose a Sylow pro-$p$ subgroup $P_p\le J$ for every $p\in\pi(J)$. Then restriction gives a well-defined bijection
--
--   $$
--   H^1(J,N)\longrightarrow\prod_{p\in\pi(J)}H^1(P_p,N)^{\mathrm{st}}.
--   $$
--
--   Here $H^1$ denotes continuous nonabelian first cohomology. A class on a subgroup $L\le J$ is $J$-stable if a representative $c$ satisfies: for every $j\in J$ there is $n_j\in N$ such that $j\cdot c(j^{-1}xj)=n_j^{-1}c(x)(x\cdot n_j)$ for all $x\in L\cap jLj^{-1}$. The superscript $\mathrm{st}$ denotes these stable classes.
--
--   This is the primary-decomposition conclusion for finite pronilpotent coefficients in the prosupersolvable semidirect-product case.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/SupersolvableCoefficients.lean, lines 12–41; source SHA-256 781403592526a9d8f37488d8af821ac2ad1e477775015b7df260546074b5b6ca.

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

theorem LocalConjugacy.Proof.LocalConjugacy.lemma_1_2_of_prosupersolvable :
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
  (hN : @LocalConjugacy.Proof.LocalConjugacy.Pronilpotent.{u_2} N inst_1 inst_4)
  (hG :
    @LocalConjugacy.Proof.LocalConjugacy.Prosupersolvable.{max u_2 u_1}
      (@LocalConjugacy.Proof.LocalConjugacy.ActionProduct.{u_1, u_2} J N inst inst_1 inst_7)
      (@SemidirectProduct.instGroup.{u_2, u_1} N J inst_1 inst
        (@MulDistribMulAction.toMulAut.{u_1, u_2} J N inst
          (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_7))
      (@LocalConjugacy.Proof.LocalConjugacy.semidirectTopology.{u_1, u_2} J N inst inst_1 inst_2 inst_4
        (@MulDistribMulAction.toMulAut.{u_1, u_2} J N inst
          (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_7)))
  (P : @LocalConjugacy.Proof.LocalConjugacy.PrimeDivisor.{u_1} J inst inst_2 → @Subgroup.{u_1} J inst)
  (hP :
    ∀ (p : @LocalConjugacy.Proof.LocalConjugacy.PrimeDivisor.{u_1} J inst inst_2),
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
            p))
        J inst inst_2 (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) (P p)),
  @LocalConjugacy.Proof.LocalConjugacy.PrimaryDecomposition.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 P := by sorry
