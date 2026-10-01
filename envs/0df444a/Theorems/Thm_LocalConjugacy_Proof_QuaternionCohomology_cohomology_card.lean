-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_QuaternionCohomology_cohomology_card
-- name    : LocalConjugacy.Proof.QuaternionCohomology.cohomology_card
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:26:50.105989+00:00
-- url     : https://prove2.me/theorems/b143d362-4dd3-4651-9d4c-6beef97cbdc2
-- title:
--   The quaternion action has two cohomology classes
-- statement:
--   Let $Q_8=\{\pm1,\pm i,\pm j,\pm k\}$ be the quaternion group, and write $S_3=\langle r,s\mid r^3=s^2=1,\ srs=r^{-1}\rangle$. Use the action in which $r$ sends $(i,j,k)$ to $(j,k,i)$ and $s$ sends $(i,j,k)$ to $(-j,-i,-k)$.
--
--   For this action, let $H^1(S_3,Q_8)$ be the set of maps $f:S_3\to Q_8$ satisfying $f(xy)=f(x)(x\cdot f(y))$, modulo the equivalence $g(x)=n^{-1}f(x)(x\cdot n)$ for one $n\in Q_8$ and all $x\in S_3$. Then
--
--   $$
--   |H^1(S_3,Q_8)|=2.
--   $$
--
--   This records the global cohomology cardinality in the quaternion example.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, QuaternionCohomology.lean, lines 19–31; source SHA-256 11136d53d4ecf66b3c7452da8d2eba6bb1188d212b4a4963d0c18b5b5d8fde02.

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

theorem LocalConjugacy.Proof.QuaternionCohomology.cohomology_card :
@Eq.{1} Nat
  (Nat.card.{0}
    (@LocalConjugacy.FiniteH1.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
      (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.action))
  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) := by sorry
