-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_sylowPro_eq_bot_of_not_primeDivisor
-- name    : LocalConjugacy.Proof.LocalConjugacy.sylowPro_eq_bot_of_not_primeDivisor
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:05:50.071798+00:00
-- url     : https://prove2.me/theorems/15dfc9f2-ee72-4b11-966c-246d479f1a69
-- title:
--   Sylow subgroups at absent quotient primes are trivial
-- statement:
--   Let $J$ be a profinite group, let $p$ be prime, and let $P$ be a Sylow pro-$p$ subgroup of $J$. Suppose that $p$ divides none of the orders $|J/U|$, where $U$ ranges over open normal subgroups of $J$. Then
--
--   $$P=\{1\}.$$
--
--   This removes primes absent from the supernatural order of the ambient profinite group from Sylow restriction arguments.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/PronilpotentSylow.lean, lines 33–49; source SHA-256 45cb1e038f2c2ddffd5cdc21dc870015e7d3ecb0b9e32bfef9fd68788e0c087a.

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

theorem LocalConjugacy.Proof.LocalConjugacy.sylowPro_eq_bot_of_not_primeDivisor :
∀ {J : Type u_1} [inst : Group.{u_1} J] [inst_1 : TopologicalSpace.{u_1} J]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_1] {p : Nat} [Fact (Nat.Prime p)]
  (P : @Subgroup.{u_1} J inst)
  (hP :
    @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1} p J inst inst_1
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) P)
  (hp :
    ∀ (U : @OpenNormalSubgroup.{u_1} J inst inst_1),
      Not
        (@Dvd.dvd.{0} Nat Nat.instDvd p
          (Nat.card.{u_1}
            (@HasQuotient.Quotient.{u_1, u_1} J (@Subgroup.{u_1} J inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} J inst)
              (@OpenSubgroup.toSubgroup.{u_1} J inst inst_1
                (@OpenNormalSubgroup.toOpenSubgroup.{u_1} J inst inst_1 U)))))),
  @Eq.{u_1 + 1} (@Subgroup.{u_1} J inst) P (@Bot.bot.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instBot.{u_1} J inst)) := by sorry
