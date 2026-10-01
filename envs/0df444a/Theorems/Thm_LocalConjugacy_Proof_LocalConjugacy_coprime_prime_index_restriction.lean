-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_coprime_prime_index_restriction
-- name    : LocalConjugacy.Proof.LocalConjugacy.coprime_prime_index_restriction
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:02:38.264568+00:00
-- url     : https://prove2.me/theorems/af0d5e83-244b-48f2-ac36-701eb7856401
-- title:
--   Cohomology restriction across a coprime prime index
-- statement:
--   Let $J$ be profinite and let $N$ be a finite discrete $p$-group on which $J$ acts continuously by automorphisms. Let $p$ and $q$ be distinct primes, and let $K\trianglelefteq J$ be closed with $[J:K]=q$. Write $H^1$ for continuous nonabelian first cohomology. Then restriction is injective and every $J$-invariant class on $K$ extends to $J$; equivalently,
--
--   $$H^1(J,N)\xrightarrow{\ \mathrm{res}\ }H^1(K,N)^J\text{ is bijective}.$$
--
--   Invariance means that for each $j\in J$, the cocycle $x\mapsto j\cdot f(j^{-1}xj)$ is cohomologous to $f$ on $K$. This supplies the prime-index step for restriction arguments with coprime coefficients.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/CoprimeRestriction.lean, lines 17–38; source SHA-256 44d17b0179d33a30d10296db1c186992bce9bce598b3e17ef941573d2e04ea1b.

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

theorem LocalConjugacy.Proof.LocalConjugacy.coprime_prime_index_restriction :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@IsTopologicalGroup.{u_2} N inst_4 inst_1] [@DiscreteTopology.{u_2} N inst_4] [Finite.{u_2 + 1} N]
  [inst_8 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [@ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_8)))
      inst_2 inst_4]
  {p q : Nat} [Fact (Nat.Prime p)] [Fact (Nat.Prime q)] (hne : @Ne.{1} Nat q p) (hN : @IsPGroup.{u_2} p N inst_1)
  (K : @Subgroup.{u_1} J inst) [@Subgroup.Normal.{u_1} J inst K]
  (hK :
    @IsClosed.{u_1} J inst_2
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) K))
  (hi : @Eq.{1} Nat (@Subgroup.index.{u_1} J inst K) q),
  @LocalConjugacy.Proof.LocalConjugacy.RestrictionIsomorphism.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_8
    (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) K
    (@le_top.{u_1} (@Subgroup.{u_1} J inst)
      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
      (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
        (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
          (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
        (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instCompleteLattice.{u_1} J inst)))
      K) := by sorry
