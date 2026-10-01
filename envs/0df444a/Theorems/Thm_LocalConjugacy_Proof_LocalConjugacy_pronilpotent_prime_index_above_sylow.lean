-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_pronilpotent_prime_index_above_sylow
-- name    : LocalConjugacy.Proof.LocalConjugacy.pronilpotent_prime_index_above_sylow
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:08:09.158298+00:00
-- url     : https://prove2.me/theorems/0119a0fc-451c-403f-8c06-5a0727cb3690
-- title:
--   A proper pronilpotent Sylow lies below a coprime prime index
-- statement:
--   Let $J$ be a pronilpotent profinite group, meaning that all its finite continuous quotients are nilpotent. Let $p$ be prime and let $P\le J$ be a proper Sylow pro-$p$ subgroup. Then
--
--   $$
--   \exists K\trianglelefteq_{\mathrm{open}}J,\qquad
--   P\le K,\quad [J:K]\text{ is prime},\quad [J:K]\ne p.
--   $$
--
--   This gives an open normal overgroup of a proper Sylow subgroup whose quotient has a different prime order.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/PronilpotentZorn.lean, lines 23–56; source SHA-256 513161a3df0f10b55069b0bafeda3c91abd1bb6268dcd7b33b0a1ec0764512d3.

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

theorem LocalConjugacy.Proof.LocalConjugacy.pronilpotent_prime_index_above_sylow :
∀ {J : Type u_1} [inst : Group.{u_1} J] [inst_1 : TopologicalSpace.{u_1} J]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_1]
  (hJ : @LocalConjugacy.Proof.LocalConjugacy.Pronilpotent.{u_1} J inst inst_1) {p : Nat} [Fact (Nat.Prime p)]
  (P : @Subgroup.{u_1} J inst)
  (hP :
    @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1} p J inst inst_1
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) P)
  (hproper :
    @Ne.{u_1 + 1} (@Subgroup.{u_1} J inst) P
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst))),
  @Exists.{u_1 + 1} (@OpenNormalSubgroup.{u_1} J inst inst_1) fun (K : @OpenNormalSubgroup.{u_1} J inst inst_1) =>
    And
      (@LE.le.{u_1} (@Subgroup.{u_1} J inst)
        (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
          (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
        P (@OpenSubgroup.toSubgroup.{u_1} J inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} J inst inst_1 K)))
      (And
        (Nat.Prime
          (@Subgroup.index.{u_1} J inst
            (@OpenSubgroup.toSubgroup.{u_1} J inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} J inst inst_1 K))))
        (@Ne.{1} Nat
          (@Subgroup.index.{u_1} J inst
            (@OpenSubgroup.toSubgroup.{u_1} J inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} J inst inst_1 K)))
          p)) := by sorry
