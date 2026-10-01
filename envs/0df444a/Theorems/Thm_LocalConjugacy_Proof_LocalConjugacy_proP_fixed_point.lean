-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_proP_fixed_point
-- name    : LocalConjugacy.Proof.LocalConjugacy.proP_fixed_point
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:00:27.33845+00:00
-- url     : https://prove2.me/theorems/7e5c8eaf-0a64-4de8-bb53-6c5771c973da
-- title:
--   A fixed point for a coprime finite pro-p action
-- statement:
--   Let $G$ be a topological group, let $p$ be prime, and assume that $G/U$ is a $p$-group for every open normal subgroup $U$ of $G$. Suppose $G$ acts on a finite set $\Omega$, every point stabilizer is closed in $G$, and $p\nmid|\Omega|$. Then
--
--   $$\exists x\in\Omega\;\forall g\in G,\qquad g\cdot x=x.$$
--
--   This converts a cardinality condition into a common fixed point. The hypotheses are expressed through open normal quotients and closed stabilizers, without requiring a topology on $\Omega$.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/ProPFixedPoint.lean, lines 11–34; source SHA-256 e0080b73f5da1d3522b096aec9a42101ece8439b8cc6de39a77a4e7330a46360.

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

theorem LocalConjugacy.Proof.LocalConjugacy.proP_fixed_point :
∀ {G : Type u_1} {Ω : Type u_2} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [@IsTopologicalGroup.{u_1} G inst_1 inst]
  [inst_3 : @MulAction.{u_1, u_2} G Ω (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))]
  [Finite.{u_2 + 1} Ω] {p : Nat} [Fact (Nat.Prime p)]
  (hG : @LocalConjugacy.Proof.LocalConjugacy.IsProP.{u_1} p G inst inst_1)
  (hc :
    ∀ (x : Ω),
      @IsClosed.{u_1} G inst_1
        (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)
          (@MulAction.stabilizer.{u_1, u_2} G Ω inst inst_3 x)))
  (hcard : Not (@Dvd.dvd.{0} Nat Nat.instDvd p (Nat.card.{u_2} Ω))),
  @Exists.{u_2 + 1} Ω fun (x : Ω) =>
    ∀ (g : G),
      @Eq.{u_2 + 1} Ω
        (@HSMul.hSMul.{u_1, u_2, u_2} G Ω Ω
          (@instHSMul.{u_1, u_2} G Ω
            (@SemigroupAction.toSMul.{u_1, u_2} G Ω
              (@Monoid.toSemigroup.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst)))
              (@MulAction.toSemigroupAction.{u_1, u_2} G Ω
                (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst)) inst_3)))
          g x)
        x := by sorry
