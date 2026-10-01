-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_HallComplementSystem_exists_compatible
-- name    : LocalConjugacy.Proof.LocalConjugacy.HallComplementSystem.exists_compatible
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:51:58.945979+00:00
-- url     : https://prove2.me/theorems/c36fd80e-78d8-4fef-9423-e724f2d0605b
-- title:
--   Compatible Hall complements containing a prescribed Sylow subgroup
-- statement:
--   Let $G$ be a prosupersolvable profinite group, let $n$ be a nonnegative integer, and let $p\le n$ be prime. Let $P$ be a Sylow pro-$p$ subgroup of $G$. For each open normal $U\trianglelefteq G$, let $M_U$ be the chosen normal Hall subgroup of $G/U$ for the primes greater than $n$, and write $\pi_U:G\to G/U$. There exist subgroups $Q_U\le G/U$ such that $Q_U$ complements $M_U$, is a Hall subgroup for the primes at most $n$, contains $\pi_U(P)$, and satisfies
--
--   $$\rho_{UV}(Q_U)=Q_V\qquad(U\le V),$$
--
--   where $\rho_{UV}:G/U\to G/V$ is the canonical map. A Hall subgroup for a set of primes has order supported on that set and index supported on its complement.
--
--   This family supplies the finite quotient data for a profinite Hall complement containing $P$.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/ProfiniteHall.lean, lines 194–210; source SHA-256 5bc8b50236c68c4f09b947c789183f5f2267a1734ba468b979d7ad6168ba9c97.

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

theorem LocalConjugacy.Proof.LocalConjugacy.HallComplementSystem.exists_compatible :
∀ {G : Type u_1} [inst : Group.{u_1} G] [inst_1 : TopologicalSpace.{u_1} G]
  [inst_2 : @LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_1]
  (hG : @LocalConjugacy.Proof.LocalConjugacy.Prosupersolvable.{u_1} G inst inst_1) (n : Nat)
  (P : @Subgroup.{u_1} G inst) {p : Nat} [Fact (Nat.Prime p)] (hpn : @LE.le.{0} Nat instLENat p n)
  (hP :
    @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1} p G inst inst_1
      (@Top.top.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instTop.{u_1} G inst)) P),
  @Exists.{u_1 + 1}
    ((U : @OpenNormalSubgroup.{u_1} G inst inst_1) →
      @LocalConjugacy.Proof.LocalConjugacy.HallComplementSystem.obj.{u_1} G inst inst_1 inst_2 hG n P U)
    fun
      (Q :
        (U : @OpenNormalSubgroup.{u_1} G inst inst_1) →
          @LocalConjugacy.Proof.LocalConjugacy.HallComplementSystem.obj.{u_1} G inst inst_1 inst_2 hG n P U) =>
    ∀ (U V : @OpenNormalSubgroup.{u_1} G inst inst_1)
      (h :
        @LE.le.{u_1} (@OpenNormalSubgroup.{u_1} G inst inst_1)
          (@Preorder.toLE.{u_1} (@OpenNormalSubgroup.{u_1} G inst inst_1)
            (@PartialOrder.toPreorder.{u_1} (@OpenNormalSubgroup.{u_1} G inst inst_1)
              (@OpenNormalSubgroup.instPartialOrderOpenNormalSubgroup.{u_1} G inst inst_1)))
          U V),
      @Eq.{u_1 + 1}
        (@Subgroup.{u_1}
          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V)))
          (@QuotientGroup.Quotient.group.{u_1} G inst
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V))
            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 V)))
        (@Subgroup.map.{u_1, u_1}
          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
          (@QuotientGroup.Quotient.group.{u_1} G inst
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V)))
          (@QuotientGroup.Quotient.group.{u_1} G inst
            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V))
            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 V))
          (@LocalConjugacy.Proof.LocalConjugacy.FiniteSylowSystem.transition.{u_1} G inst inst_1 U V h)
          (@Subtype.val.{u_1 + 1}
            (@Subgroup.{u_1}
              (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
              (@QuotientGroup.Quotient.group.{u_1} G inst
                (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                  (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
            (fun
                (Q :
                  @Subgroup.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))) =>
              And
                (@Subgroup.IsComplement'.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                  (@LocalConjugacy.Proof.LocalConjugacy.finiteUpperHall.{u_1} G inst inst_1 inst_2 hG n U) Q)
                (And
                  (@LocalConjugacy.Proof.LocalConjugacy.IsHall.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                    (@Set.ofPred.{0} Nat fun (r : Nat) => @LE.le.{0} Nat instLENat r n) Q)
                  (@LE.le.{u_1}
                    (@Subgroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                    (@Preorder.toLE.{u_1}
                      (@Subgroup.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                      (@PartialOrder.toPreorder.{u_1}
                        (@Subgroup.{u_1}
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))
                        (@Subgroup.instPartialOrder.{u_1}
                          (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                            (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                          (@QuotientGroup.Quotient.group.{u_1} G inst
                            (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                              (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                            (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U)))))
                    (@Subgroup.map.{u_1, u_1} G inst
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                      (@QuotientGroup.mk'.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 U))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 U))
                      P)
                    Q)))
            (Q U)))
        (@Subtype.val.{u_1 + 1}
          (@Subgroup.{u_1}
            (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
              (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V)))
            (@QuotientGroup.Quotient.group.{u_1} G inst
              (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1 (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V))
              (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 V)))
          (fun
              (Q :
                @Subgroup.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 V))) =>
            And
              (@Subgroup.IsComplement'.{u_1}
                (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                  (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V)))
                (@QuotientGroup.Quotient.group.{u_1} G inst
                  (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                    (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V))
                  (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 V))
                (@LocalConjugacy.Proof.LocalConjugacy.finiteUpperHall.{u_1} G inst inst_1 inst_2 hG n V) Q)
              (And
                (@LocalConjugacy.Proof.LocalConjugacy.IsHall.{u_1}
                  (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                    (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V)))
                  (@QuotientGroup.Quotient.group.{u_1} G inst
                    (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                      (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V))
                    (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 V))
                  (@Set.ofPred.{0} Nat fun (r : Nat) => @LE.le.{0} Nat instLENat r n) Q)
                (@LE.le.{u_1}
                  (@Subgroup.{u_1}
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 V)))
                  (@Preorder.toLE.{u_1}
                    (@Subgroup.{u_1}
                      (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                        (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V)))
                      (@QuotientGroup.Quotient.group.{u_1} G inst
                        (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                          (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V))
                        (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 V)))
                    (@PartialOrder.toPreorder.{u_1}
                      (@Subgroup.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 V)))
                      (@Subgroup.instPartialOrder.{u_1}
                        (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                          (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V)))
                        (@QuotientGroup.Quotient.group.{u_1} G inst
                          (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                            (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V))
                          (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 V)))))
                  (@Subgroup.map.{u_1, u_1} G inst
                    (@HasQuotient.Quotient.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@QuotientGroup.instHasQuotientSubgroup.{u_1} G inst)
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V)))
                    (@QuotientGroup.Quotient.group.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 V))
                    (@QuotientGroup.mk'.{u_1} G inst
                      (@OpenSubgroup.toSubgroup.{u_1} G inst inst_1
                        (@OpenNormalSubgroup.toOpenSubgroup.{u_1} G inst inst_1 V))
                      (@OpenNormalSubgroup.instNormal.{u_1} G inst inst_1 V))
                    P)
                  Q)))
          (Q V)) := by sorry
