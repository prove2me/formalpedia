-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_exists_finite_invariant_coefficient_subgroup
-- name    : LocalConjugacy.Proof.LocalConjugacy.exists_finite_invariant_coefficient_subgroup
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:55:13.627982+00:00
-- url     : https://prove2.me/theorems/7f1329a0-11bc-4c93-970f-549173e1a5b8
-- title:
--   Finite invariant coefficient subgroups
-- statement:
--   Let $J$ be a group endowed with a compact topology and acting continuously by automorphisms on a discrete group $N$. Assume that $N$ is locally finite, meaning that every finite subset generates a finite subgroup. For every finite subset $s\subseteq N$, there exists a subgroup $M\le N$ such that
--
--   $$|M|<\infty,\qquad s\subseteq M,\qquad j\cdot M=M\quad(j\in J).$$
--
--   This places finitely many coefficients inside a finite subgroup preserved by the full action, enabling reduction to finite coefficients.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/FiniteCoefficientSubgroup.lean, lines 19–43; source SHA-256 ecacaf6eb618b08ef0d4465d2779b846d038e8790596f76a1129c1a49c1da6e3.

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

theorem LocalConjugacy.Proof.LocalConjugacy.exists_finite_invariant_coefficient_subgroup :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [@CompactSpace.{u_1} J inst_2] [inst_4 : TopologicalSpace.{u_2} N] [@DiscreteTopology.{u_2} N inst_4]
  [inst_6 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [@ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_6)))
      inst_2 inst_4]
  (hN : @LocalConjugacy.Proof.LocalConjugacy.LocallyFiniteGroup.{u_2} N inst_1) (s : Set.{u_2} N)
  (hs : @Set.Finite.{u_2} N s),
  @Exists.{u_2 + 1} (@Subgroup.{u_2} N inst_1) fun (M : @Subgroup.{u_2} N inst_1) =>
    And
      (Finite.{u_2 + 1}
        (@Subtype.{u_2 + 1} N fun (x : N) =>
          @Membership.mem.{u_2, u_2} N (@Subgroup.{u_2} N inst_1)
            (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} N inst_1) N (@Subgroup.instSetLike.{u_2} N inst_1)) M
            x))
      (And
        (@LE.le.{u_2} (Set.{u_2} N) (@Set.instLE.{u_2} N) s
          (@SetLike.coe.{u_2, u_2} (@Subgroup.{u_2} N inst_1) N (@Subgroup.instSetLike.{u_2} N inst_1) M))
        (∀ (j : J) (n : N),
          @Membership.mem.{u_2, u_2} N (@Subgroup.{u_2} N inst_1)
              (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} N inst_1) N (@Subgroup.instSetLike.{u_2} N inst_1)) M
              n →
            @Membership.mem.{u_2, u_2} N (@Subgroup.{u_2} N inst_1)
              (@SetLike.instMembership.{u_2, u_2} (@Subgroup.{u_2} N inst_1) N (@Subgroup.instSetLike.{u_2} N inst_1)) M
              (@HSMul.hSMul.{u_1, u_2, u_2} J N N
                (@instHSMul.{u_1, u_2} J N
                  (@SemigroupAction.toSMul.{u_1, u_2} J N
                    (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
                    (@MulAction.toSemigroupAction.{u_1, u_2} J N
                      (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                      (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
                        (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                        (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_6))))
                j n))) := by sorry
