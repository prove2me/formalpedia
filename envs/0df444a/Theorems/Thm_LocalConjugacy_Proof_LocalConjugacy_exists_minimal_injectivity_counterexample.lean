-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_exists_minimal_injectivity_counterexample
-- name    : LocalConjugacy.Proof.LocalConjugacy.exists_minimal_injectivity_counterexample
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:03:32.710115+00:00
-- url     : https://prove2.me/theorems/28245c63-1ef2-473d-9d21-a2a831adc796
-- title:
--   A minimal subgroup preserving failure of injectivity
-- statement:
--   Let $J$ be a profinite group acting continuously by automorphisms on a discrete group $N$. Let $P\le J$, and let $f,g:J\to N$ be continuous nonabelian cocycles. Assume that their restrictions to $P$ are cohomologous, but $f$ and $g$ are not cohomologous on $J$. Then there exists a closed subgroup $L\le J$ with
--
--   $$P<L,\qquad [f|_L]\ne[g|_L],\qquad [f|_K]=[g|_K]\ \text{for every closed }K\text{ with }P\le K<L.$$
--
--   Brackets denote cohomology classes: $[u]=[v]$ means $v(x)=n^{-1}u(x)(x\cdot n)$ for one fixed $n\in N$ and every element of the domain. This isolates an inclusion-minimal obstruction for the specified pair of cocycles.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/CocycleZorn.lean, lines 114–140; source SHA-256 e1e12eb6db3f14e77d7b32521dedaac1aaa35f2d93a22daf6f1432f8e67d8240.

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

theorem LocalConjugacy.Proof.LocalConjugacy.exists_minimal_injectivity_counterexample :
∀ {J : Type u_1} {N : Type u_2} [inst : Group.{u_1} J] [inst_1 : Group.{u_2} N] [inst_2 : TopologicalSpace.{u_1} J]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} J inst inst_2] [inst_4 : TopologicalSpace.{u_2} N]
  [@DiscreteTopology.{u_2} N inst_4]
  [inst_6 :
    @MulDistribMulAction.{u_1, u_2} J N (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
      (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1))]
  [@ContinuousSMul.{u_1, u_2} J N
      (@SemigroupAction.toSMul.{u_1, u_2} J N
        (@Monoid.toSemigroup.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst)))
        (@MulAction.toSemigroupAction.{u_1, u_2} J N
          (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
          (@MulDistribMulAction.toMulAction.{u_1, u_2} J N
            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))
            (@DivInvMonoid.toMonoid.{u_2} N (@Group.toDivInvMonoid.{u_2} N inst_1)) inst_6)))
      inst_2 inst_4]
  (P : @Subgroup.{u_1} J inst)
  (f g :
    @LocalConjugacy.Proof.LocalConjugacy.Cocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6
      (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)))
  (hP :
    @LocalConjugacy.Proof.LocalConjugacy.Cohomologous.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 P
      (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 P
        (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst))
        (have this :
          @LE.le.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            P (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) :=
          @le_top.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
              (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
              (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                (@Subgroup.instCompleteLattice.{u_1} J inst)))
            P;
        this)
        f)
      (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 P
        (@Top.top.{u_1} (@Subgroup.{u_1} J inst)
          (@OrderTop.toTop.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
              (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
              (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                (@Subgroup.instCompleteLattice.{u_1} J inst)))))
        (@le_top.{u_1} (@Subgroup.{u_1} J inst)
          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
          (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
            (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
              (@Subgroup.instCompleteLattice.{u_1} J inst)))
          P)
        g))
  (hbad :
    Not
      (@LocalConjugacy.Proof.LocalConjugacy.Cohomologous.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6
        (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) f g)),
  @Exists.{u_1 + 1} (@Subgroup.{u_1} J inst) fun (L : @Subgroup.{u_1} J inst) =>
    And
      (@IsClosed.{u_1} J inst_2
        (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) L))
      (And
        (@LT.lt.{u_1} (@Subgroup.{u_1} J inst)
          (@Preorder.toLT.{u_1} (@Subgroup.{u_1} J inst)
            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
          P L)
        (And
          (Not
            (@LocalConjugacy.Proof.LocalConjugacy.Cohomologous.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 L
              (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 L
                (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst))
                (have this :
                  @LE.le.{u_1} (@Subgroup.{u_1} J inst)
                    (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                      (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                        (@Subgroup.instPartialOrder.{u_1} J inst)))
                    L (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) :=
                  @le_top.{u_1} (@Subgroup.{u_1} J inst)
                    (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                      (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                        (@Subgroup.instPartialOrder.{u_1} J inst)))
                    (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
                      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                          (@Subgroup.instPartialOrder.{u_1} J inst)))
                      (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                        (@Subgroup.instCompleteLattice.{u_1} J inst)))
                    L;
                this)
                f)
              (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 L
                (@Top.top.{u_1} (@Subgroup.{u_1} J inst)
                  (@OrderTop.toTop.{u_1} (@Subgroup.{u_1} J inst)
                    (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                      (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                        (@Subgroup.instPartialOrder.{u_1} J inst)))
                    (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
                      (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                        (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                          (@Subgroup.instPartialOrder.{u_1} J inst)))
                      (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                        (@Subgroup.instCompleteLattice.{u_1} J inst)))))
                (@le_top.{u_1} (@Subgroup.{u_1} J inst)
                  (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                    (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
                  (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
                    (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                      (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                        (@Subgroup.instPartialOrder.{u_1} J inst)))
                    (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                      (@Subgroup.instCompleteLattice.{u_1} J inst)))
                  L)
                g)))
          (∀ (K : @Subgroup.{u_1} J inst),
            @IsClosed.{u_1} J inst_2
                (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst) K) →
              @LE.le.{u_1} (@Subgroup.{u_1} J inst)
                  (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                    (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instPartialOrder.{u_1} J inst)))
                  P K →
                @LT.lt.{u_1} (@Subgroup.{u_1} J inst)
                    (@Preorder.toLT.{u_1} (@Subgroup.{u_1} J inst)
                      (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                        (@Subgroup.instPartialOrder.{u_1} J inst)))
                    K L →
                  @LocalConjugacy.Proof.LocalConjugacy.Cohomologous.{u_1, u_2} J N inst inst_1 inst_2 inst_4 inst_6 K
                    (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4
                      inst_6 K (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst))
                      (have this :
                        @LE.le.{u_1} (@Subgroup.{u_1} J inst)
                          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                              (@Subgroup.instPartialOrder.{u_1} J inst)))
                          K (@Top.top.{u_1} (@Subgroup.{u_1} J inst) (@Subgroup.instTop.{u_1} J inst)) :=
                        @le_top.{u_1} (@Subgroup.{u_1} J inst)
                          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                              (@Subgroup.instPartialOrder.{u_1} J inst)))
                          (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
                            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                                (@Subgroup.instPartialOrder.{u_1} J inst)))
                            (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                              (@Subgroup.instCompleteLattice.{u_1} J inst)))
                          K;
                      this)
                      f)
                    (@LocalConjugacy.Proof.LocalConjugacy.restrictCocycle.{u_1, u_2} J N inst inst_1 inst_2 inst_4
                      inst_6 K
                      (@Top.top.{u_1} (@Subgroup.{u_1} J inst)
                        (@OrderTop.toTop.{u_1} (@Subgroup.{u_1} J inst)
                          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                              (@Subgroup.instPartialOrder.{u_1} J inst)))
                          (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
                            (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                              (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                                (@Subgroup.instPartialOrder.{u_1} J inst)))
                            (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                              (@Subgroup.instCompleteLattice.{u_1} J inst)))))
                      (@le_top.{u_1} (@Subgroup.{u_1} J inst)
                        (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                          (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                            (@Subgroup.instPartialOrder.{u_1} J inst)))
                        (@BoundedOrder.toOrderTop.{u_1} (@Subgroup.{u_1} J inst)
                          (@Preorder.toLE.{u_1} (@Subgroup.{u_1} J inst)
                            (@PartialOrder.toPreorder.{u_1} (@Subgroup.{u_1} J inst)
                              (@Subgroup.instPartialOrder.{u_1} J inst)))
                          (@CompleteLattice.toBoundedOrder.{u_1} (@Subgroup.{u_1} J inst)
                            (@Subgroup.instCompleteLattice.{u_1} J inst)))
                        K)
                      g)))) := by sorry
