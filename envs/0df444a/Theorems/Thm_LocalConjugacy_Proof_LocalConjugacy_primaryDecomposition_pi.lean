-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_primaryDecomposition_pi
-- name    : LocalConjugacy.Proof.LocalConjugacy.primaryDecomposition_pi
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:06:03.51745+00:00
-- url     : https://prove2.me/theorems/06c05a12-7724-4137-bd4c-b1646b95a432
-- title:
--   Primary decomposition for products of coefficient groups
-- statement:
--   Let $J$ be a group equipped with a topology, let $I$ be any index set, and for each $i\in I$ let $N_i$ be a group equipped with a topology and an action of $J$ by automorphisms. Choose subgroups $P_p\le J$ indexed by $p\in\pi(J)$. Suppose continuous cocycle restriction gives primary decomposition with coefficients in every $N_i$: it lands in stable classes and is bijective onto their product. Give $N=\prod_{i\in I}N_i$ the product topology and coordinatewise action. Then
--
--   $$H^1(J,N)\xrightarrow{\ \mathrm{res}\ }\prod_{p\in\pi(J)}H^1(P_p,N)^{\mathrm{st},J}\text{ is bijective}.$$
--
--   Here $\pi(J)$ consists of primes dividing $|J/U|_{\mathrm{fin}}$ for some open normal subgroup $U$; $|X|_{\mathrm{fin}}$ is the size of a finite set $X$ and is $0$ when $X$ is infinite.
--
--   A class on $P_p$ is $J$-stable if, for each $j\in J$, its cocycle and the conjugate cocycle $x\mapsto j\cdot f(j^{-1}xj)$ differ by one coboundary on $P_p\cap jP_pj^{-1}$.
--
--   This assembles primary decomposition for separate coefficient factors into primary decomposition for their full product.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/CocycleProducts.lean, lines 51–71; source SHA-256 a22c54d6bc561966f7182beeb7cee3c100acaf190accf29bb2f3efb491284a89.

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

theorem LocalConjugacy.Proof.LocalConjugacy.primaryDecomposition_pi :
∀ {J : Type u_1} [inst : Group.{u_1} J] [inst_1 : TopologicalSpace.{u_1} J] {ι : Type u_2} {N : ι → Type u_3}
  [inst_2 : (i : ι) → Group.{u_3} (N i)] [inst_3 : (i : ι) → TopologicalSpace.{u_3} (N i)]
  [inst_4 :
    (i : ι) →
      @MulDistribMulAction.{u_1, u_3} J (N i) (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
        (@DivInvMonoid.toMonoid.{u_3} (N i) (@Group.toDivInvMonoid.{u_3} (N i) (inst_2 i)))]
  (P : @LocalConjugacy.Proof.LocalConjugacy.PrimeDivisor.{u_1} J inst inst_1 → @Subgroup.{u_1} J inst)
  (h :
    ∀ (i : ι),
      @LocalConjugacy.Proof.LocalConjugacy.PrimaryDecomposition.{u_1, u_3} J (N i) inst (inst_2 i) inst_1 (inst_3 i)
        (inst_4 i) P),
  @LocalConjugacy.Proof.LocalConjugacy.PrimaryDecomposition.{u_1, max u_2 u_3} J ((i : ι) → N i) inst
    (@Pi.group.{u_2, u_3} ι N inst_2) inst_1 (@Pi.topologicalSpace.{u_3, u_2} ι N inst_3)
    (@Pi.mulDistribMulAction.{u_2, u_3, u_1} ι N J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (fun (i : ι) =>
        @DivInvMonoid.toMonoid.{u_3} (N i) ((fun (i : ι) => @Group.toDivInvMonoid.{u_3} (N i) (inst_2 i)) i))
      inst_4)
    P := by sorry
