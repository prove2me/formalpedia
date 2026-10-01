-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_FiniteAbelianCohomology_norm_coboundary
-- name    : LocalConjugacy.Proof.LocalConjugacy.FiniteAbelianCohomology.norm_coboundary
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:51:34.100985+00:00
-- url     : https://prove2.me/theorems/1b718d10-f8af-46e3-932d-a8821f2bbb0c
-- title:
--   A subgroup index annihilates a locally trivial abelian cocycle
-- statement:
--   Let $J$ be a finite group, $A$ an abelian group written multiplicatively, and $a:J\to\operatorname{Aut}(A)$ an action. Let $f:J\to A$ satisfy $f(xy)=f(x)a(x)(f(y))$. Suppose $P\le J$ and $n\in A$ satisfy $f(x)a(x)(n)=n$ for every $x\in P$. Then
--
--   $$
--   \exists b\in A\quad\forall x\in J,\qquad f(x)^{[J:P]}=b^{-1}a(x)(b).
--   $$
--
--   This converts triviality after restriction to $P$ into annihilation of the global cohomology class by the subgroup index.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/FiniteAbelianCohomology.lean, lines 23–63; source SHA-256 cccc1bfb2eddaf9628e01b39707b6f4006b1322fd0203f1e3b24b465fed75afc.

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

theorem LocalConjugacy.Proof.LocalConjugacy.FiniteAbelianCohomology.norm_coboundary :
∀ {J : Type u_1} {A : Type u_2} [inst : Group.{u_1} J] [inst_1 : CommGroup.{u_2} A] [Fintype.{u_1} J]
  (a :
    @MonoidHom.{u_1, u_2} J
      (@MulAut.{u_2} A
        (@MulOne.toMul.{u_2} A
          (@MulOneClass.toMulOne.{u_2} A
            (@Monoid.toMulOneClass.{u_2} A
              (@DivInvMonoid.toMonoid.{u_2} A (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
      (@MulOneClass.toMulOne.{u_1} J
        (@Monoid.toMulOneClass.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))))
      (@MulOneClass.toMulOne.{u_2}
        (@MulAut.{u_2} A
          (@MulOne.toMul.{u_2} A
            (@MulOneClass.toMulOne.{u_2} A
              (@Monoid.toMulOneClass.{u_2} A
                (@DivInvMonoid.toMonoid.{u_2} A (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
        (@Monoid.toMulOneClass.{u_2}
          (@MulAut.{u_2} A
            (@MulOne.toMul.{u_2} A
              (@MulOneClass.toMulOne.{u_2} A
                (@Monoid.toMulOneClass.{u_2} A
                  (@DivInvMonoid.toMonoid.{u_2} A
                    (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
          (@DivInvMonoid.toMonoid.{u_2}
            (@MulAut.{u_2} A
              (@MulOne.toMul.{u_2} A
                (@MulOneClass.toMulOne.{u_2} A
                  (@Monoid.toMulOneClass.{u_2} A
                    (@DivInvMonoid.toMonoid.{u_2} A
                      (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
            (@Group.toDivInvMonoid.{u_2}
              (@MulAut.{u_2} A
                (@MulOne.toMul.{u_2} A
                  (@MulOneClass.toMulOne.{u_2} A
                    (@Monoid.toMulOneClass.{u_2} A
                      (@DivInvMonoid.toMonoid.{u_2} A
                        (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
              (@MulAut.instGroup.{u_2} A
                (@MulOne.toMul.{u_2} A
                  (@MulOneClass.toMulOne.{u_2} A
                    (@Monoid.toMulOneClass.{u_2} A
                      (@DivInvMonoid.toMonoid.{u_2} A
                        (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))))))))
  (f : J → A)
  (hf : @LocalConjugacy.Proof.LocalConjugacy.CocycleFn.{u_1, u_2} J A inst (@CommGroup.toGroup.{u_2} A inst_1) a f)
  (P : @Subgroup.{u_1} J inst) (n : A)
  (hP :
    ∀
      (x :
        @Subtype.{u_1 + 1} J fun (x : J) =>
          @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
            (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) P x),
      @Eq.{u_2 + 1} A
        (@HMul.hMul.{u_2, u_2, u_2} A A A
          (@instHMul.{u_2} A
            (@MulOne.toMul.{u_2} A
              (@MulOneClass.toMulOne.{u_2} A
                (@Monoid.toMulOneClass.{u_2} A
                  (@DivInvMonoid.toMonoid.{u_2} A
                    (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
          (f
            (@Subtype.val.{u_1 + 1} J
              (fun (x : J) =>
                @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                  (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst)) P
                  x)
              x))
          (@DFunLike.coe.{u_2 + 1, u_2 + 1, u_2 + 1}
            (@MulEquiv.{u_2, u_2} A A
              (@MulOne.toMul.{u_2} A
                (@MulOneClass.toMulOne.{u_2} A
                  (@Monoid.toMulOneClass.{u_2} A
                    (@DivInvMonoid.toMonoid.{u_2} A
                      (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))
              (@MulOne.toMul.{u_2} A
                (@MulOneClass.toMulOne.{u_2} A
                  (@Monoid.toMulOneClass.{u_2} A
                    (@DivInvMonoid.toMonoid.{u_2} A
                      (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
            A (fun (x : A) => A)
            (@EquivLike.toFunLike.{u_2 + 1, u_2 + 1, u_2 + 1}
              (@MulEquiv.{u_2, u_2} A A
                (@MulOne.toMul.{u_2} A
                  (@MulOneClass.toMulOne.{u_2} A
                    (@Monoid.toMulOneClass.{u_2} A
                      (@DivInvMonoid.toMonoid.{u_2} A
                        (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))
                (@MulOne.toMul.{u_2} A
                  (@MulOneClass.toMulOne.{u_2} A
                    (@Monoid.toMulOneClass.{u_2} A
                      (@DivInvMonoid.toMonoid.{u_2} A
                        (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
              A A
              (@MulEquiv.instEquivLike.{u_2, u_2} A A
                (@MulOne.toMul.{u_2} A
                  (@MulOneClass.toMulOne.{u_2} A
                    (@Monoid.toMulOneClass.{u_2} A
                      (@DivInvMonoid.toMonoid.{u_2} A
                        (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))
                (@MulOne.toMul.{u_2} A
                  (@MulOneClass.toMulOne.{u_2} A
                    (@Monoid.toMulOneClass.{u_2} A
                      (@DivInvMonoid.toMonoid.{u_2} A
                        (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))))
            (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
              (@MonoidHom.{u_1, u_2} J
                (@MulAut.{u_2} A
                  (@MulOne.toMul.{u_2} A
                    (@MulOneClass.toMulOne.{u_2} A
                      (@Monoid.toMulOneClass.{u_2} A
                        (@DivInvMonoid.toMonoid.{u_2} A
                          (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                (@MulOneClass.toMulOne.{u_1} J
                  (@Monoid.toMulOneClass.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))))
                (@MulOneClass.toMulOne.{u_2}
                  (@MulAut.{u_2} A
                    (@MulOne.toMul.{u_2} A
                      (@MulOneClass.toMulOne.{u_2} A
                        (@Monoid.toMulOneClass.{u_2} A
                          (@DivInvMonoid.toMonoid.{u_2} A
                            (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                  (@Monoid.toMulOneClass.{u_2}
                    (@MulAut.{u_2} A
                      (@MulOne.toMul.{u_2} A
                        (@MulOneClass.toMulOne.{u_2} A
                          (@Monoid.toMulOneClass.{u_2} A
                            (@DivInvMonoid.toMonoid.{u_2} A
                              (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                    (@DivInvMonoid.toMonoid.{u_2}
                      (@MulAut.{u_2} A
                        (@MulOne.toMul.{u_2} A
                          (@MulOneClass.toMulOne.{u_2} A
                            (@Monoid.toMulOneClass.{u_2} A
                              (@DivInvMonoid.toMonoid.{u_2} A
                                (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                      (@Group.toDivInvMonoid.{u_2}
                        (@MulAut.{u_2} A
                          (@MulOne.toMul.{u_2} A
                            (@MulOneClass.toMulOne.{u_2} A
                              (@Monoid.toMulOneClass.{u_2} A
                                (@DivInvMonoid.toMonoid.{u_2} A
                                  (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                        (@MulAut.instGroup.{u_2} A
                          (@MulOne.toMul.{u_2} A
                            (@MulOneClass.toMulOne.{u_2} A
                              (@Monoid.toMulOneClass.{u_2} A
                                (@DivInvMonoid.toMonoid.{u_2} A
                                  (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))))))))
              J
              (fun (x : J) =>
                @MulAut.{u_2} A
                  (@MulOne.toMul.{u_2} A
                    (@MulOneClass.toMulOne.{u_2} A
                      (@Monoid.toMulOneClass.{u_2} A
                        (@DivInvMonoid.toMonoid.{u_2} A
                          (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
              (@MonoidHom.instFunLike.{u_1, u_2} J
                (@MulAut.{u_2} A
                  (@MulOne.toMul.{u_2} A
                    (@MulOneClass.toMulOne.{u_2} A
                      (@Monoid.toMulOneClass.{u_2} A
                        (@DivInvMonoid.toMonoid.{u_2} A
                          (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                (@MulOneClass.toMulOne.{u_1} J
                  (@Monoid.toMulOneClass.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))))
                (@MulOneClass.toMulOne.{u_2}
                  (@MulAut.{u_2} A
                    (@MulOne.toMul.{u_2} A
                      (@MulOneClass.toMulOne.{u_2} A
                        (@Monoid.toMulOneClass.{u_2} A
                          (@DivInvMonoid.toMonoid.{u_2} A
                            (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                  (@Monoid.toMulOneClass.{u_2}
                    (@MulAut.{u_2} A
                      (@MulOne.toMul.{u_2} A
                        (@MulOneClass.toMulOne.{u_2} A
                          (@Monoid.toMulOneClass.{u_2} A
                            (@DivInvMonoid.toMonoid.{u_2} A
                              (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                    (@DivInvMonoid.toMonoid.{u_2}
                      (@MulAut.{u_2} A
                        (@MulOne.toMul.{u_2} A
                          (@MulOneClass.toMulOne.{u_2} A
                            (@Monoid.toMulOneClass.{u_2} A
                              (@DivInvMonoid.toMonoid.{u_2} A
                                (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                      (@Group.toDivInvMonoid.{u_2}
                        (@MulAut.{u_2} A
                          (@MulOne.toMul.{u_2} A
                            (@MulOneClass.toMulOne.{u_2} A
                              (@Monoid.toMulOneClass.{u_2} A
                                (@DivInvMonoid.toMonoid.{u_2} A
                                  (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                        (@MulAut.instGroup.{u_2} A
                          (@MulOne.toMul.{u_2} A
                            (@MulOneClass.toMulOne.{u_2} A
                              (@Monoid.toMulOneClass.{u_2} A
                                (@DivInvMonoid.toMonoid.{u_2} A
                                  (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))))))))
              a
              (@Subtype.val.{u_1 + 1} J
                (fun (x : J) =>
                  @Membership.mem.{u_1, u_1} J (@Subgroup.{u_1} J inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} J inst) J (@Subgroup.instSetLike.{u_1} J inst))
                    P x)
                x))
            n))
        n),
  @Exists.{u_2 + 1} A fun (b : A) =>
    ∀ (x : J),
      @Eq.{u_2 + 1} A
        (@HPow.hPow.{u_2, 0, u_2} A Nat A
          (@instHPow.{u_2, 0} A Nat
            (@NPow.toPow.{u_2} A
              (@Monoid.toNPow.{u_2} A
                (@DivInvMonoid.toMonoid.{u_2} A (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))
          (f x) (@Subgroup.index.{u_1} J inst P))
        (@HMul.hMul.{u_2, u_2, u_2} A A A
          (@instHMul.{u_2} A
            (@MulOne.toMul.{u_2} A
              (@MulOneClass.toMulOne.{u_2} A
                (@Monoid.toMulOneClass.{u_2} A
                  (@DivInvMonoid.toMonoid.{u_2} A
                    (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
          (@Inv.inv.{u_2} A
            (@InvOneClass.toInv.{u_2} A
              (@DivInvOneMonoid.toInvOneClass.{u_2} A
                (@DivisionMonoid.toDivInvOneMonoid.{u_2} A
                  (@DivisionCommMonoid.toDivisionMonoid.{u_2} A (@CommGroup.toDivisionCommMonoid.{u_2} A inst_1)))))
            b)
          (@DFunLike.coe.{u_2 + 1, u_2 + 1, u_2 + 1}
            (@MulEquiv.{u_2, u_2} A A
              (@MulOne.toMul.{u_2} A
                (@MulOneClass.toMulOne.{u_2} A
                  (@Monoid.toMulOneClass.{u_2} A
                    (@DivInvMonoid.toMonoid.{u_2} A
                      (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))
              (@MulOne.toMul.{u_2} A
                (@MulOneClass.toMulOne.{u_2} A
                  (@Monoid.toMulOneClass.{u_2} A
                    (@DivInvMonoid.toMonoid.{u_2} A
                      (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
            A (fun (x : A) => A)
            (@EquivLike.toFunLike.{u_2 + 1, u_2 + 1, u_2 + 1}
              (@MulEquiv.{u_2, u_2} A A
                (@MulOne.toMul.{u_2} A
                  (@MulOneClass.toMulOne.{u_2} A
                    (@Monoid.toMulOneClass.{u_2} A
                      (@DivInvMonoid.toMonoid.{u_2} A
                        (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))
                (@MulOne.toMul.{u_2} A
                  (@MulOneClass.toMulOne.{u_2} A
                    (@Monoid.toMulOneClass.{u_2} A
                      (@DivInvMonoid.toMonoid.{u_2} A
                        (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
              A A
              (@MulEquiv.instEquivLike.{u_2, u_2} A A
                (@MulOne.toMul.{u_2} A
                  (@MulOneClass.toMulOne.{u_2} A
                    (@Monoid.toMulOneClass.{u_2} A
                      (@DivInvMonoid.toMonoid.{u_2} A
                        (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))
                (@MulOne.toMul.{u_2} A
                  (@MulOneClass.toMulOne.{u_2} A
                    (@Monoid.toMulOneClass.{u_2} A
                      (@DivInvMonoid.toMonoid.{u_2} A
                        (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))))
            (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
              (@MonoidHom.{u_1, u_2} J
                (@MulAut.{u_2} A
                  (@MulOne.toMul.{u_2} A
                    (@MulOneClass.toMulOne.{u_2} A
                      (@Monoid.toMulOneClass.{u_2} A
                        (@DivInvMonoid.toMonoid.{u_2} A
                          (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                (@MulOneClass.toMulOne.{u_1} J
                  (@Monoid.toMulOneClass.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))))
                (@MulOneClass.toMulOne.{u_2}
                  (@MulAut.{u_2} A
                    (@MulOne.toMul.{u_2} A
                      (@MulOneClass.toMulOne.{u_2} A
                        (@Monoid.toMulOneClass.{u_2} A
                          (@DivInvMonoid.toMonoid.{u_2} A
                            (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                  (@Monoid.toMulOneClass.{u_2}
                    (@MulAut.{u_2} A
                      (@MulOne.toMul.{u_2} A
                        (@MulOneClass.toMulOne.{u_2} A
                          (@Monoid.toMulOneClass.{u_2} A
                            (@DivInvMonoid.toMonoid.{u_2} A
                              (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                    (@DivInvMonoid.toMonoid.{u_2}
                      (@MulAut.{u_2} A
                        (@MulOne.toMul.{u_2} A
                          (@MulOneClass.toMulOne.{u_2} A
                            (@Monoid.toMulOneClass.{u_2} A
                              (@DivInvMonoid.toMonoid.{u_2} A
                                (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                      (@Group.toDivInvMonoid.{u_2}
                        (@MulAut.{u_2} A
                          (@MulOne.toMul.{u_2} A
                            (@MulOneClass.toMulOne.{u_2} A
                              (@Monoid.toMulOneClass.{u_2} A
                                (@DivInvMonoid.toMonoid.{u_2} A
                                  (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                        (@MulAut.instGroup.{u_2} A
                          (@MulOne.toMul.{u_2} A
                            (@MulOneClass.toMulOne.{u_2} A
                              (@Monoid.toMulOneClass.{u_2} A
                                (@DivInvMonoid.toMonoid.{u_2} A
                                  (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))))))))
              J
              (fun (x : J) =>
                @MulAut.{u_2} A
                  (@MulOne.toMul.{u_2} A
                    (@MulOneClass.toMulOne.{u_2} A
                      (@Monoid.toMulOneClass.{u_2} A
                        (@DivInvMonoid.toMonoid.{u_2} A
                          (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
              (@MonoidHom.instFunLike.{u_1, u_2} J
                (@MulAut.{u_2} A
                  (@MulOne.toMul.{u_2} A
                    (@MulOneClass.toMulOne.{u_2} A
                      (@Monoid.toMulOneClass.{u_2} A
                        (@DivInvMonoid.toMonoid.{u_2} A
                          (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                (@MulOneClass.toMulOne.{u_1} J
                  (@Monoid.toMulOneClass.{u_1} J (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))))
                (@MulOneClass.toMulOne.{u_2}
                  (@MulAut.{u_2} A
                    (@MulOne.toMul.{u_2} A
                      (@MulOneClass.toMulOne.{u_2} A
                        (@Monoid.toMulOneClass.{u_2} A
                          (@DivInvMonoid.toMonoid.{u_2} A
                            (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                  (@Monoid.toMulOneClass.{u_2}
                    (@MulAut.{u_2} A
                      (@MulOne.toMul.{u_2} A
                        (@MulOneClass.toMulOne.{u_2} A
                          (@Monoid.toMulOneClass.{u_2} A
                            (@DivInvMonoid.toMonoid.{u_2} A
                              (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                    (@DivInvMonoid.toMonoid.{u_2}
                      (@MulAut.{u_2} A
                        (@MulOne.toMul.{u_2} A
                          (@MulOneClass.toMulOne.{u_2} A
                            (@Monoid.toMulOneClass.{u_2} A
                              (@DivInvMonoid.toMonoid.{u_2} A
                                (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                      (@Group.toDivInvMonoid.{u_2}
                        (@MulAut.{u_2} A
                          (@MulOne.toMul.{u_2} A
                            (@MulOneClass.toMulOne.{u_2} A
                              (@Monoid.toMulOneClass.{u_2} A
                                (@DivInvMonoid.toMonoid.{u_2} A
                                  (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1)))))))
                        (@MulAut.instGroup.{u_2} A
                          (@MulOne.toMul.{u_2} A
                            (@MulOneClass.toMulOne.{u_2} A
                              (@Monoid.toMulOneClass.{u_2} A
                                (@DivInvMonoid.toMonoid.{u_2} A
                                  (@Group.toDivInvMonoid.{u_2} A (@CommGroup.toGroup.{u_2} A inst_1))))))))))))
              a x)
            b)) := by sorry
