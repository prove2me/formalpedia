-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_primaryRestriction_bijective
-- name    : LocalConjugacy.Proof.LocalConjugacy.primaryRestriction_bijective
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:23:19.828984+00:00
-- url     : https://prove2.me/theorems/6f03021f-1870-46c2-91ca-fb42dd1609ba
-- title:
--   Primary decomposition induces a bijection on cohomology classes
-- statement:
--   Let $J,N$ be groups equipped with topologies, with an action of $J$ on $N$ by automorphisms, and choose subgroups $P_p\le J$ for $p\in\pi(J)$. Assume primary decomposition on continuous cocycle representatives: every global restriction is stable; two global cocycles with cohomologous restrictions at every $p$ are cohomologous; and every family of stable cocycles on the $P_p$ is obtained, up to cohomology, by restriction of a global cocycle. Then simultaneous restriction is bijective:
--
--   $$H^1(J,N)\xrightarrow{\ \mathrm{res}\ }\prod_{p\in\pi(J)}H^1(P_p,N)^{\mathrm{st},J}.$$
--
--   Here $\pi(J)$ consists of primes dividing $|J/U|_{\mathrm{fin}}$ for some open normal subgroup $U$; $|X|_{\mathrm{fin}}$ is the size of a finite set $X$ and is $0$ when $X$ is infinite.
--
--   A class on $P_p$ is $J$-stable if, for each $j\in J$, its cocycle and the conjugate cocycle $x\mapsto j\cdot f(j^{-1}xj)$ differ by one coboundary on $P_p\cap jP_pj^{-1}$.
--
--   This turns the representative-level property into the corresponding statement about the actual quotient sets of cohomology classes.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/ManuscriptCohomology.lean, lines 34–54; source SHA-256 4031dfc77f6ddab910a5fe8591d717af4d515a69e5dd43e367263473cd845502.

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

theorem LocalConjugacy.Proof.LocalConjugacy.primaryRestriction_bijective :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [inst_3 : TopologicalSpace.{u_2} N]
  [inst_4 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  (P : @LocalConjugacy.Proof.LocalConjugacy.PrimeDivisor.{u_1} J inst inst_2 → @Subgroup.{u_1} J inst)
  (h : @LocalConjugacy.Proof.LocalConjugacy.PrimaryDecomposition.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4 P),
  @Function.Bijective.{max (u_1 + 1) (u_2 + 1), max (u_1 + 1) (u_2 + 1)}
    (@LocalConjugacy.Proof.LocalConjugacy.H1.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)))
    ((p : @LocalConjugacy.Proof.LocalConjugacy.PrimeDivisor.{u_1} J inst inst_2) →
      @LocalConjugacy.Proof.LocalConjugacy.InvariantH1.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4
        (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) (P p))
    (@LocalConjugacy.Proof.LocalConjugacy.primaryRestriction.{u_1, u_2} J N inst inst_1 inst_2 inst_3 inst_4 P) := by sorry
