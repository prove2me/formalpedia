-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_primaryDecomposition_of_equiv
-- name    : LocalConjugacy.Proof.LocalConjugacy.primaryDecomposition_of_equiv
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:05:27.376784+00:00
-- url     : https://prove2.me/theorems/3d342c8e-abc6-41a1-8907-2e332375f084
-- title:
--   Primary decomposition is preserved by coefficient isomorphisms
-- statement:
--   Let $J,N,M$ be groups equipped with topologies, and let $J$ act by automorphisms on $N$ and $M$. Choose subgroups $P_p\le J$ indexed by $p\in\pi(J)$. Let $e:N\to M$ be a group isomorphism such that $e$ and $e^{-1}$ are continuous and $e(j\cdot n)=j\cdot e(n)$ for all $j,n$. Suppose continuous cocycle restriction gives primary decomposition for $M$: it lands in $J$-stable classes, is injective, and every family of stable classes occurs. Then the same holds for $N$:
--
--   $$H^1(J,N)\xrightarrow{\ \mathrm{res}\ }\prod_{p\in\pi(J)}H^1(P_p,N)^{\mathrm{st},J}\text{ is bijective}.$$
--
--   Here $\pi(J)$ consists of primes dividing $|J/U|_{\mathrm{fin}}$ for some open normal subgroup $U$; $|X|_{\mathrm{fin}}$ is the size of a finite set $X$ and is $0$ when $X$ is infinite.
--
--   A class on $P_p$ is $J$-stable if, for each $j\in J$, its cocycle and the conjugate cocycle $x\mapsto j\cdot f(j^{-1}xj)$ differ by one coboundary on $P_p\cap jP_pj^{-1}$.
--
--   This transports primary decomposition across an equivariant homeomorphic group isomorphism of coefficients.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/CocycleProducts.lean, lines 112–143; source SHA-256 a22c54d6bc561966f7182beeb7cee3c100acaf190accf29bb2f3efb491284a89.

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

universe u_1 u_2 u_3

theorem LocalConjugacy.Proof.LocalConjugacy.primaryDecomposition_of_equiv :
∀ {J : Type u_1} {N : Type u_2} {M : Type u_3} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : Group.{u_3} M]
  [inst_3 : TopologicalSpace.{u_1} J] [inst_4 : TopologicalSpace.{u_2} N] [inst_5 : TopologicalSpace.{u_3} M]
  [inst_6 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [inst_7 :
    @MulDistribMulAction.{u_1, u_3} J M (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2))]
  (P : @LocalConjugacy.Proof.LocalConjugacy.PrimeDivisor.{u_1} J inst inst_3 → @Subgroup.{u_1} J inst)
  (e :
    @MulEquiv.{u_2, u_3} N M
      (@MulOne.toMul.{u_2} N
        (@MulOneClass.toMulOne.{u_2} N
          (@Monoid.toMulOneClass.{u_2} N (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
      (@MulOne.toMul.{u_3} M
        (@MulOneClass.toMulOne.{u_3} M
          (@Monoid.toMulOneClass.{u_3} M (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2))))))
  (he :
    @Continuous.{u_2, u_3} N M inst_4 inst_5
      (@DFunLike.coe.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
        (@MulEquiv.{u_2, u_3} N M
          (@MulOne.toMul.{u_2} N
            (@MulOneClass.toMulOne.{u_2} N
              (@Monoid.toMulOneClass.{u_2} N (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
          (@MulOne.toMul.{u_3} M
            (@MulOneClass.toMulOne.{u_3} M
              (@Monoid.toMulOneClass.{u_3} M (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2))))))
        N (fun (x : N) => M)
        (@EquivLike.toFunLike.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
          (@MulEquiv.{u_2, u_3} N M
            (@MulOne.toMul.{u_2} N
              (@MulOneClass.toMulOne.{u_2} N
                (@Monoid.toMulOneClass.{u_2} N
                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
            (@MulOne.toMul.{u_3} M
              (@MulOneClass.toMulOne.{u_3} M
                (@Monoid.toMulOneClass.{u_3} M
                  (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2))))))
          N M
          (@MulEquiv.instEquivLike.{u_2, u_3} N M
            (@MulOne.toMul.{u_2} N
              (@MulOneClass.toMulOne.{u_2} N
                (@Monoid.toMulOneClass.{u_2} N
                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
            (@MulOne.toMul.{u_3} M
              (@MulOneClass.toMulOne.{u_3} M
                (@Monoid.toMulOneClass.{u_3} M
                  (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2)))))))
        e))
  (hei :
    @Continuous.{u_3, u_2} M N inst_5 inst_4
      (@DFunLike.coe.{max (u_3 + 1) (u_2 + 1), u_3 + 1, u_2 + 1}
        (@MulEquiv.{u_3, u_2} M N
          (@MulOne.toMul.{u_3} M
            (@MulOneClass.toMulOne.{u_3} M
              (@Monoid.toMulOneClass.{u_3} M (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2)))))
          (@MulOne.toMul.{u_2} N
            (@MulOneClass.toMulOne.{u_2} N
              (@Monoid.toMulOneClass.{u_2} N (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
        M (fun (x : M) => N)
        (@EquivLike.toFunLike.{max (u_3 + 1) (u_2 + 1), u_3 + 1, u_2 + 1}
          (@MulEquiv.{u_3, u_2} M N
            (@MulOne.toMul.{u_3} M
              (@MulOneClass.toMulOne.{u_3} M
                (@Monoid.toMulOneClass.{u_3} M
                  (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2)))))
            (@MulOne.toMul.{u_2} N
              (@MulOneClass.toMulOne.{u_2} N
                (@Monoid.toMulOneClass.{u_2} N
                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))))))
          M N
          (@MulEquiv.instEquivLike.{u_3, u_2} M N
            (@MulOne.toMul.{u_3} M
              (@MulOneClass.toMulOne.{u_3} M
                (@Monoid.toMulOneClass.{u_3} M
                  (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2)))))
            (@MulOne.toMul.{u_2} N
              (@MulOneClass.toMulOne.{u_2} N
                (@Monoid.toMulOneClass.{u_2} N
                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))))
        (@MulEquiv.symm.{u_2, u_3} N M
          (@MulOne.toMul.{u_2} N
            (@MulOneClass.toMulOne.{u_2} N
              (@Monoid.toMulOneClass.{u_2} N (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
          (@MulOne.toMul.{u_3} M
            (@MulOneClass.toMulOne.{u_3} M
              (@Monoid.toMulOneClass.{u_3} M (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2)))))
          e)))
  (ha :
    ∀ (j : J) (n : N),
      @Eq.{u_3 + 1} M
        (@DFunLike.coe.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
          (@MulEquiv.{u_2, u_3} N M
            (@MulOne.toMul.{u_2} N
              (@MulOneClass.toMulOne.{u_2} N
                (@Monoid.toMulOneClass.{u_2} N
                  (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
            (@MulOne.toMul.{u_3} M
              (@MulOneClass.toMulOne.{u_3} M
                (@Monoid.toMulOneClass.{u_3} M
                  (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2))))))
          N (fun (x : N) => M)
          (@EquivLike.toFunLike.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
            (@MulEquiv.{u_2, u_3} N M
              (@MulOne.toMul.{u_2} N
                (@MulOneClass.toMulOne.{u_2} N
                  (@Monoid.toMulOneClass.{u_2} N
                    (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
              (@MulOne.toMul.{u_3} M
                (@MulOneClass.toMulOne.{u_3} M
                  (@Monoid.toMulOneClass.{u_3} M
                    (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2))))))
            N M
            (@MulEquiv.instEquivLike.{u_2, u_3} N M
              (@MulOne.toMul.{u_2} N
                (@MulOneClass.toMulOne.{u_2} N
                  (@Monoid.toMulOneClass.{u_2} N
                    (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
              (@MulOne.toMul.{u_3} M
                (@MulOneClass.toMulOne.{u_3} M
                  (@Monoid.toMulOneClass.{u_3} M
                    (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2)))))))
          e
          (@HSMul.hSMul.{u_1, u_2, u_2} J N N
            (@instHSMul.{u_1, u_2} J N
              (@SemigroupAction.toSMul.{u_1, u_2} J N
                (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
                (@MulAction.toSemigroupAction.{u_1, u_2} J N
                  (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                  (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
                    (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                    (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_6))))
            j n))
        (@HSMul.hSMul.{u_1, u_3, u_3} J M M
          (@instHSMul.{u_1, u_3} J M
            (@SemigroupAction.toSMul.{u_1, u_3} J M
              (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
              (@MulAction.toSemigroupAction.{u_1, u_3} J M
                (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                (@MulDistribMulAction.toMulAction.{u_1, u_3} J M
                  (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
                  (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2)) inst_7))))
          j
          (@DFunLike.coe.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
            (@MulEquiv.{u_2, u_3} N M
              (@MulOne.toMul.{u_2} N
                (@MulOneClass.toMulOne.{u_2} N
                  (@Monoid.toMulOneClass.{u_2} N
                    (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
              (@MulOne.toMul.{u_3} M
                (@MulOneClass.toMulOne.{u_3} M
                  (@Monoid.toMulOneClass.{u_3} M
                    (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2))))))
            N (fun (x : N) => M)
            (@EquivLike.toFunLike.{max (u_2 + 1) (u_3 + 1), u_2 + 1, u_3 + 1}
              (@MulEquiv.{u_2, u_3} N M
                (@MulOne.toMul.{u_2} N
                  (@MulOneClass.toMulOne.{u_2} N
                    (@Monoid.toMulOneClass.{u_2} N
                      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
                (@MulOne.toMul.{u_3} M
                  (@MulOneClass.toMulOne.{u_3} M
                    (@Monoid.toMulOneClass.{u_3} M
                      (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2))))))
              N M
              (@MulEquiv.instEquivLike.{u_2, u_3} N M
                (@MulOne.toMul.{u_2} N
                  (@MulOneClass.toMulOne.{u_2} N
                    (@Monoid.toMulOneClass.{u_2} N
                      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)))))
                (@MulOne.toMul.{u_3} M
                  (@MulOneClass.toMulOne.{u_3} M
                    (@Monoid.toMulOneClass.{u_3} M
                      (@DivInvMonoid.toMonoid.{u_3} M (@Group.toDivInvMonoid.{u_3} M inst_2)))))))
            e n)))
  (h : @LocalConjugacy.Proof.LocalConjugacy.PrimaryDecomposition.{u_1, u_3} J M inst inst_2 inst_3 inst_5 inst_7 P),
  @LocalConjugacy.Proof.LocalConjugacy.PrimaryDecomposition.{u_1, u_2} J N inst inst_1 inst_3 inst_4 inst_6 P := by sorry
