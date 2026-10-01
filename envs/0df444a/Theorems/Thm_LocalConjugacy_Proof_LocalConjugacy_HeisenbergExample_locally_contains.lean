-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_HeisenbergExample_locally_contains
-- name    : LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.locally_contains
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:51:50.407656+00:00
-- url     : https://prove2.me/theorems/dce014c3-4a57-480e-a2b2-b2c95cad7a0a
-- title:
--   Local containment in the Heisenberg example
-- statement:
--   Let $G=C_3\wr S_3=C_3^3\rtimes S_3$ act on $\Omega=\mathbb F_3\times\mathbb F_3$ by $(b,\sigma)(u,v)=(\sigma u,b_{\sigma u}+v)$. Let $H$ be the stabilizer of $(0,0)$. Let $c$ translate the second coordinate only in block $0$, let $t$ interchange blocks $1$ and $2$ without translating, and put $J=\langle c,t\rangle$. Equip this finite group with the discrete topology. Then $H$ locally contains $J$:
--
--   $$
--   \forall p\text{ prime},\quad\exists P\in\operatorname{Syl}_p(J),\ \exists g\in G,\qquad gPg^{-1}\le H.
--   $$
--
--   This supplies the local-containment assertion for the explicit Heisenberg counterexample.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/Counterexamples/Heisenberg.lean, lines 211–231; source SHA-256 748e762c138403c7d0d1173608f4cb098848b36b93692f9218b98f20c4e4e0ba.

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

theorem LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.locally_contains :
@LocalConjugacy.Proof.LocalConjugacy.LocallyContains.{0} LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.G
  (@SemidirectProduct.instGroup.{0, 0} LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.B
    LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.S
    (@Pi.group.{0, 0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (fun (a : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) =>
        LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.C3)
      fun (i : ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) =>
      @Multiplicative.group.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@AddGroupWithOne.toAddGroup.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          (@Ring.toAddGroupWithOne.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (@DivisionRing.toRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (@Field.toDivisionRing.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  Nat.fact_prime_three))))))
    (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
    LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.action)
  LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.instTopologicalSpaceG
  LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.H LocalConjugacy.Proof.LocalConjugacy.HeisenbergExample.J := by sorry
