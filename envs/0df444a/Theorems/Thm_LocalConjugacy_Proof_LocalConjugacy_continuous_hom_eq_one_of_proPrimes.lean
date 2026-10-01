-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_continuous_hom_eq_one_of_proPrimes
-- name    : LocalConjugacy.Proof.LocalConjugacy.continuous_hom_eq_one_of_proPrimes
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:53:40.456843+00:00
-- url     : https://prove2.me/theorems/83a03d3e-00eb-477d-95c2-e729ea0d63ba
-- title:
--   Vanishing of homomorphisms with disjoint quotient primes
-- statement:
--   Let $G$ be a group endowed with a topology, let $N$ be a discrete $p$-group for a prime $p$, and let $\pi\subseteq\mathbb N$ with $p\notin\pi$. Assume that for every open normal subgroup $U$ of $G$, every prime divisor of $\operatorname{Nat.card}(G/U)$ belongs to $\pi$. Here $\operatorname{Nat.card}$ is the cardinality for a finite set and $0$ for an infinite set. For every continuous homomorphism $f:G\to N$,
--
--   $$\forall x\in G,\qquad f(x)=1.$$
--
--   This gives coprime vanishing for homomorphisms without requiring the discrete coefficient group to be finite.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/HallCohomology.lean, lines 87–104; source SHA-256 1d0d103e9a2c5244bd52aed3275317c01a49cfbe4a4703658b6cab294aa0e8bf.

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

theorem LocalConjugacy.Proof.LocalConjugacy.continuous_hom_eq_one_of_proPrimes :
∀ {G : Type u_1} {N : Type u_2} [inst : Group.{u_1} G] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} G]
  [inst_3 : TopologicalSpace.{u_2} N] [@DiscreteTopology.{u_2} N inst_3] {π : Set.{0} Nat} {p : Nat}
  [hp : Fact (Nat.Prime p)] (hG : @LocalConjugacy.Proof.LocalConjugacy.HasProPrimes.{u_1} π G inst inst_2)
  (hpπ : Not (@Membership.mem.{0, 0} Nat (Set.{0} Nat) (@Set.instMembership.{0} Nat) π p))
  (hN : @IsPGroup.{u_2} p N inst_1)
  (f :
    @MonoidHom.{u_1, u_2} G N
      (@MulOneClass.toMulOne.{u_1} G
        (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))
      (@MulOneClass.toMulOne.{u_2} N
        (@Monoid.toMulOneClass.{u_2} N (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
  (hf :
    @Continuous.{u_1, u_2} G N inst_2 inst_3
      (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
        (@MonoidHom.{u_1, u_2} G N
          (@MulOneClass.toMulOne.{u_1} G
            (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))
          (@MulOneClass.toMulOne.{u_2} N
            (@Monoid.toMulOneClass.{u_2} N (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
        G (fun (x : G) => N)
        (@MonoidHom.instFunLike.{u_1, u_2} G N
          (@MulOneClass.toMulOne.{u_1} G
            (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))
          (@MulOneClass.toMulOne.{u_2} N
            (@Monoid.toMulOneClass.{u_2} N (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
        f))
  (x : G),
  @Eq.{u_2 + 1} N
    (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
      (@MonoidHom.{u_1, u_2} G N
        (@MulOneClass.toMulOne.{u_1} G
          (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))
        (@MulOneClass.toMulOne.{u_2} N
          (@Monoid.toMulOneClass.{u_2} N (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
      G (fun (x : G) => N)
      (@MonoidHom.instFunLike.{u_1, u_2} G N
        (@MulOneClass.toMulOne.{u_1} G
          (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))
        (@MulOneClass.toMulOne.{u_2} N
          (@Monoid.toMulOneClass.{u_2} N (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
      f x)
    (@OfNat.ofNat.{u_2} N (nat_lit 1)
      (@One.toOfNat1.{u_2} N
        (@InvOneClass.toOne.{u_2} N
          (@DivInvOneMonoid.toInvOneClass.{u_2} N
            (@DivisionMonoid.toDivInvOneMonoid.{u_2} N (@Group.toDivisionMonoid.{u_2} N inst_1)))))) := by sorry
