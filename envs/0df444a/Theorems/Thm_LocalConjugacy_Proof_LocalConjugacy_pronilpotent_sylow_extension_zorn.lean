-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_pronilpotent_sylow_extension_zorn
-- name    : LocalConjugacy.Proof.LocalConjugacy.pronilpotent_sylow_extension_zorn
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:09:08.336078+00:00
-- url     : https://prove2.me/theorems/cea4f3c5-38ce-4ff8-8d9b-1a18ff351325
-- title:
--   Stable Sylow classes extend in pronilpotent groups
-- statement:
--   Let $J$ be a pronilpotent profinite group, let $p$ be prime, and let $N$ be a finite discrete $p$-group with a continuous action of $J$ by automorphisms. Let $P$ be a Sylow pro-$p$ subgroup of $J$, and let $\tau:P\to N$ be a continuous $1$-cocycle. Assume that for every $j\in J$ there is $n_j\in N$ such that $j\cdot\tau(j^{-1}xj)=n_j^{-1}\tau(x)(x\cdot n_j)$ whenever $x\in P\cap jPj^{-1}$. Then
--
--   $$\exists F\in Z^1_{\mathrm{cts}}(J,N),\qquad [F|_P]=[\tau]\text{ in }H^1(P,N).$$
--
--   Here $Z^1_{\mathrm{cts}}$ denotes continuous cocycles and square brackets denote their cohomology classes. This gives extension of each stable Sylow class in the pronilpotent restriction theorem.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/PronilpotentZorn.lean, lines 95–138; source SHA-256 513161a3df0f10b55069b0bafeda3c91abd1bb6268dcd7b33b0a1ec0764512d3.

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

theorem LocalConjugacy.Proof.LocalConjugacy.pronilpotent_sylow_extension_zorn :
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
  (hJ : @LocalConjugacy.Proof.LocalConjugacy.Pronilpotent.{u_1} J inst inst_2) {p : Nat} [Fact (Nat.Prime p)]
  (hN : @IsPGroup.{u_2} p N inst_1) (P : @Subgroup.{u_1} J inst)
  (hP :
    @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1} p J inst inst_2
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) P)
  (τ : @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 P)
  (hτ :
    @LocalConjugacy.Proof.LocalConjugacy.InvariantUnder.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) P τ),
  @LocalConjugacy.Proof.LocalConjugacy.Cocycle.ExtendsTo.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 P τ
    (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) := by sorry
