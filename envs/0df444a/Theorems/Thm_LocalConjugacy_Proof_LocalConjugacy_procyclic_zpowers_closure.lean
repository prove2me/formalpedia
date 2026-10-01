-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_procyclic_zpowers_closure
-- name    : LocalConjugacy.Proof.LocalConjugacy.procyclic_zpowers_closure
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:01:08.608922+00:00
-- url     : https://prove2.me/theorems/b65b80ad-1ef7-4188-af6f-f8200b93ccd6
-- title:
--   The closure of a cyclic subgroup is procyclic
-- statement:
--   Let $G$ be a profinite group and let $x\in G$. Let $C=\overline{\langle x\rangle}$, with the subgroup topology inherited from $G$. Then
--
--   $$C\text{ is procyclic}.$$
--
--   Here procyclic means that some element of $C$ generates a dense cyclic subgroup. This produces a procyclic subgroup from a chosen ambient element.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/ProcyclicSupplement.lean, lines 14–26; source SHA-256 429ecddcbffd2706e842f6a56760d47bb060b391d61fde1a939c585260614f00.

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

theorem LocalConjugacy.Proof.LocalConjugacy.procyclic_zpowers_closure :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [inst_2 : @LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1] (x : G),
  @LocalConjugacy.Proof.LocalConjugacy.Procyclic.{u_1}
    (@Subtype.{u_1 + 1} G fun (x_1 : G) =>
      @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
        (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
        (@Subgroup.topologicalClosure.{u_1} G inst_1 inst
          (@LocalConjugacy.Proof.LocalConjugacy.Profinite.toIsTopologicalGroup.{u_1} G inst inst_1 inst_2)
          (@Subgroup.zpowers.{u_1} G inst x))
        x_1)
    (@Subgroup.toGroup.{u_1} G inst
      (@Subgroup.topologicalClosure.{u_1} G inst_1 inst
        (@LocalConjugacy.Proof.LocalConjugacy.Profinite.toIsTopologicalGroup.{u_1} G inst inst_1 inst_2)
        (@Subgroup.zpowers.{u_1} G inst x)))
    (@instTopologicalSpaceSubtype.{u_1} G
      (fun (x_1 : G) =>
        @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst))
          (@Subgroup.topologicalClosure.{u_1} G inst_1 inst
            (@LocalConjugacy.Proof.LocalConjugacy.Profinite.toIsTopologicalGroup.{u_1} G inst inst_1 inst_2)
            (@Subgroup.zpowers.{u_1} G inst x))
          x_1)
      inst_1) := by sorry
