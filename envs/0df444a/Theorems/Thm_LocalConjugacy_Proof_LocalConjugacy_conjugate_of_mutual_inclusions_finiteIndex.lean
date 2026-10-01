-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_conjugate_of_mutual_inclusions_finiteIndex
-- name    : LocalConjugacy.Proof.LocalConjugacy.conjugate_of_mutual_inclusions_finiteIndex
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:53:31.461984+00:00
-- url     : https://prove2.me/theorems/aee22227-7d7a-4517-9be3-fe7d51b458da
-- title:
--   Mutual conjugate inclusions imply finite-index conjugacy
-- statement:
--   Let $H$ and $K$ be finite-index subgroups of a group $G$. Suppose there are $a,b\in G$ with $aHa^{-1}\le K$ and $bKb^{-1}\le H$. Then
--
--   $$
--   \exists g\in G,\qquad gHg^{-1}=K.
--   $$
--
--   This upgrades conjugate containment in both directions to conjugacy when the subgroup indices are finite.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/FiniteKernelTools.lean, lines 72–87; source SHA-256 d52afafade269acd8512c3b357588ee8fbc72b6710e28852052150018abe41ea.

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

theorem LocalConjugacy.Proof.LocalConjugacy.conjugate_of_mutual_inclusions_finiteIndex :
∀ {G : Type u_1} [inst : Group.{u_1} G] (H K : @Subgroup.{u_1} G inst) [@Subgroup.FiniteIndex.{u_1} G inst H]
  [@Subgroup.FiniteIndex.{u_1} G inst K]
  (hHK :
    @Exists.{u_1 + 1} G fun (g : G) =>
      @LE.le.{u_1} (@Subgroup.{u_1} G inst)
        (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
          (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
        (@LocalConjugacy.Proof.LocalConjugacy.conjugate.{u_1} G inst g H) K)
  (hKH :
    @Exists.{u_1 + 1} G fun (g : G) =>
      @LE.le.{u_1} (@Subgroup.{u_1} G inst)
        (@Preorder.toLE.{u_1} (@Subgroup.{u_1} G inst)
          (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instPartialOrder.{u_1} G inst)))
        (@LocalConjugacy.Proof.LocalConjugacy.conjugate.{u_1} G inst g K) H),
  @LocalConjugacy.Proof.LocalConjugacy.Conjugate.{u_1} G inst H K := by sorry
