-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_fixed_cocycle_of_locallyFinite
-- name    : LocalConjugacy.Proof.LocalConjugacy.fixed_cocycle_of_locallyFinite
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:55:53.962179+00:00
-- url     : https://prove2.me/theorems/2e3bbea6-36e3-4fa7-a058-6d408cf986a3
-- title:
--   Fixed representatives with locally finite coefficients
-- statement:
--   Let $J$ be a profinite group acting continuously by automorphisms on a discrete, locally finite $p$-group $N$, where $p$ is prime; locally finite means every finitely generated subgroup is finite. Let $q\ne p$ be prime, $K\trianglelefteq J$ a closed subgroup, and $Q\le J$ a procyclic pro-$q$ subgroup with the inherited topology. For a continuous cocycle $f:K\to N$, define $(T_{q'}f)(x)=q'\cdot f((q')^{-1}xq')$ for $q'\in Q$. Assume every $T_{q'}f$ is cohomologous to $f$. Then
--
--   $$
--   \exists g\in Z^1_{\mathrm{cts}}(K,N),\qquad [g]=[f],\qquad T_{q'}g=g\ \text{for all }q'\in Q.
--   $$
--
--   Here procyclic means that one element generates a dense cyclic subgroup, and pro-$q$ means every open normal quotient is a $q$-group. This gives a fixed cocycle representative even when the coefficient group is infinite.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/LocallyFiniteCocycles.lean, lines 18–53; source SHA-256 1decfecb3c106e19af299b48417a3a48800fc6eb09cf183261dc3fc16336a5e1.

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

theorem LocalConjugacy.Proof.LocalConjugacy.fixed_cocycle_of_locallyFinite :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [inst_3 : @LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@IsTopologicalGroup.{u_2} N inst_4 inst_1] [@DiscreteTopology.{u_2} N inst_4]
  [inst_7 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [inst_8 :
    @ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_7)))
      inst_2 inst_4]
  (hfinite : @LocalConjugacy.Proof.LocalConjugacy.LocallyFiniteGroup.{u_2} N inst_1) {p q : Nat} [Fact (Nat.Prime p)]
  [Fact (Nat.Prime q)] (hne : @Ne.{1} Nat q p) (hN : @IsPGroup.{u_2} p N inst_1) {K : @Subgroup.{u_1} J inst}
  [inst_11 : @Subgroup.Normal.{u_1} J inst K]
  (hK :
    @IsClosed.{u_1} J inst_2
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) K))
  (Q : @Subgroup.{u_1} J inst)
  (hcyclic :
    @LocalConjugacy.Proof.LocalConjugacy.Procyclic.{u_1}
      (@Subtype.{u_1 + 1} J fun (x : J) =>
        @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
      (@Subgroup.toGroup.{u_1} J inst Q)
      (@instTopologicalSpaceSubtype.{u_1} J
        (fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
        inst_2))
  (hQ :
    @LocalConjugacy.Proof.LocalConjugacy.IsProP.{u_1} q
      (@Subtype.{u_1 + 1} J fun (x : J) =>
        @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
          (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
      (@Subgroup.toGroup.{u_1} J inst Q)
      (@instTopologicalSpaceSubtype.{u_1} J
        (fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x)
        inst_2))
  (f : @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 K)
  (hinv : @LocalConjugacy.Proof.LocalConjugacy.InvariantUnder.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 Q K f),
  @Exists.{max (u_1 + 1) (u_2 + 1)}
    (@LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 K)
    fun (g : @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 K) =>
    And (@LocalConjugacy.Proof.LocalConjugacy.Cohomologous.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 K f g)
      (∀
        (x :
          @Subtype.{u_1 + 1} J fun (x : J) =>
            @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
              (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q x),
        @Eq.{max (u_1 + 1) (u_2 + 1)}
          (@LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_7 K)
          (@LocalConjugacy.Proof.LocalConjugacy.twistCocycle.{u_1, u_2} J N inst inst_1 inst_2
            (@LocalConjugacy.Proof.LocalConjugacy.Profinite.toIsTopologicalGroup.{u_1} J inst inst_2 inst_3) inst_4
            inst_7 inst_8 K inst_11 g
            (@Subtype.val.{u_1 + 1} J
              (fun (x : J) =>
                @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) Q
                  x)
              x))
          g) := by sorry
