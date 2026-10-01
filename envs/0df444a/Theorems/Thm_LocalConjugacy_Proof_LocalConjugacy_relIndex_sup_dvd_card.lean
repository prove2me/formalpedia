-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_relIndex_sup_dvd_card
-- name    : LocalConjugacy.Proof.LocalConjugacy.relIndex_sup_dvd_card
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:24:42.737011+00:00
-- url     : https://prove2.me/theorems/dea0aa5d-9fa5-4e4b-aa3d-c9e95c8e35c0
-- title:
--   The index after adjoining a normal subgroup divides its order
-- statement:
--   Let $G$ be a finite group, $A\trianglelefteq G$, and $H\le G$. Then
--
--   $$
--   [\langle A,H\rangle:H]\mid |A|.
--   $$
--
--   This controls the relative index created by adjoining a normal subgroup and supports finite-group induction arguments.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/SupplementInductionTools.lean, lines 88–102; source SHA-256 106dcf452b6af3be9bdd0e61c7f1c1f0b774d4f83a49826dcb6d4dc1ae59aa0a.

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

theorem LocalConjugacy.Proof.LocalConjugacy.relIndex_sup_dvd_card :
∀ {G : Type u_1} [inst : Group.{u_1} G] [Finite.{u_1 + 1} G] (A H : @Subgroup.{u_1} G inst)
  [@Subgroup.Normal.{u_1} G inst A],
  @Dvd.dvd.{0} Nat Nat.instDvd
    (@Subgroup.relIndex.{u_1} G inst H
      (@Max.max.{u_1} (@Subgroup.{u_1} G inst)
        (@SemilatticeSup.toMax.{u_1} (@Subgroup.{u_1} G inst)
          (@Lattice.toSemilatticeSup.{u_1} (@Subgroup.{u_1} G inst)
            (@ConditionallyCompleteLattice.toLattice.{u_1} (@Subgroup.{u_1} G inst)
              (@CompleteLattice.toConditionallyCompleteLattice.{u_1} (@Subgroup.{u_1} G inst)
                (@Subgroup.instCompleteLattice.{u_1} G inst)))))
        A H))
    (Nat.card.{u_1}
      (@Subtype.{u_1 + 1} G fun (x : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst)) A x)) := by sorry
