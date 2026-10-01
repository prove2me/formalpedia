-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_QuaternionComplements_locallyConjugate
-- name    : LocalConjugacy.Proof.QuaternionComplements.locallyConjugate
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:31:58.419597+00:00
-- url     : https://prove2.me/theorems/a66cf841-8ce5-48f3-bb3d-fea99620fcfc
-- title:
--   The quaternion complements are locally conjugate
-- statement:
--   Let $Q_8=\{\pm1,\pm i,\pm j,\pm k\}$ be the quaternion group, and write $S_3=\langle r,s\mid r^3=s^2=1,\ srs=r^{-1}\rangle$. Use the action in which $r$ sends $(i,j,k)$ to $(j,k,i)$ and $s$ sends $(i,j,k)$ to $(-j,-i,-k)$.
--
--   Form $G=Q_8\rtimes S_3$. Let $\varepsilon:S_3\to\{1,-1\}\le Q_8$ be the sign character, and define the two subgroups $J_0=\{(1,x):x\in S_3\}$ and $J_1=\{(\varepsilon(x),x):x\in S_3\}$. Then
--
--   $$
--   \forall p\text{ prime},\quad\exists P\in\operatorname{Syl}_p(J_0),\ Q\in\operatorname{Syl}_p(J_1),\ g\in G,\qquad gPg^{-1}=Q.
--   $$
--
--   This establishes the local-conjugacy half of the quaternion complement counterexample.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, QuaternionComplements.lean, lines 60–92; source SHA-256 7f35368846c08698e08cd573f38e777715e417617117caf395e0c80f56c00bf4.

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

theorem LocalConjugacy.Proof.QuaternionComplements.locallyConjugate :
@LocalConjugacy.FiniteLocallyConjugate.{0}
  (@SemidirectProduct.{0, 0} LocalConjugacy.Q8 LocalConjugacy.S3
    (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    LocalConjugacy.Proof.quaternionAction)
  (@SemidirectProduct.instGroup.{0, 0} LocalConjugacy.Q8 LocalConjugacy.S3
    (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
    LocalConjugacy.Proof.quaternionAction)
  (LocalConjugacy.quaternionComplement LocalConjugacy.Proof.quaternionAction)
  LocalConjugacy.Proof.QuaternionComplements.secondComplement := by sorry
