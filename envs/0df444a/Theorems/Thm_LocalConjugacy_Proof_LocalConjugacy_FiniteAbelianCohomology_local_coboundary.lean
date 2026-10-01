-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_FiniteAbelianCohomology_local_coboundary
-- name    : LocalConjugacy.Proof.LocalConjugacy.FiniteAbelianCohomology.local_coboundary
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:51:47.699426+00:00
-- url     : https://prove2.me/theorems/b43000dc-4f1f-4e25-9a88-c5e61c8ab90b
-- title:
--   Sylow-local vanishing for finite abelian coefficients
-- statement:
--   Let $J$ be a finite group, let $A$ be a finite abelian group, and let $a:J\to\operatorname{Aut}(A)$ be an action. Suppose $f:J\to A$ satisfies $f(xy)=f(x)a(x)(f(y))$. Assume that for every prime $p$ there are a Sylow $p$-subgroup $P\le J$ and $n\in A$ such that $f(x)a(x)(n)=n$ for every $x\in P$. Then
--
--   $$\exists b\in A\;\forall x\in J,\qquad f(x)=b^{-1}a(x)(b).$$
--
--   This detects triviality of a cohomology class from its restrictions to one Sylow subgroup at each prime.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/FiniteAbelianCohomology.lean, lines 65–89; source SHA-256 cccc1bfb2eddaf9628e01b39707b6f4006b1322fd0203f1e3b24b465fed75afc.

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

theorem LocalConjugacy.Proof.LocalConjugacy.FiniteAbelianCohomology.local_coboundary :
∀ {J : Type u_1} {A : Type u_2} [inst : Group.{u_1} J] [inst_1 : CommGroup.{u_2} A] [Fintype.{u_1} J]
  [Finite.{u_2 + 1} A]
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
  (hloc :
    ∀ (p : Nat),
      Nat.Prime p →
        @Exists.{u_1 + 1} (@Sylow.{u_1} p J inst) fun (P : @Sylow.{u_1} p J inst) =>
          @Exists.{u_2 + 1} A fun (n : A) =>
            ∀
              (x :
                @Subtype.{u_1 + 1} J fun (x : J) =>
                  @Membership.mem.{u_1, u_1} J (@Sylow.{u_1} p J inst)
                    (@SetLike.instMembership.{u_1, u_1} (@Sylow.{u_1} p J inst) J (@Sylow.instSetLike.{u_1} p J inst)) P
                    x),
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
                        @Membership.mem.{u_1, u_1} J (@Sylow.{u_1} p J inst)
                          (@SetLike.instMembership.{u_1, u_1} (@Sylow.{u_1} p J inst) J
                            (@Sylow.instSetLike.{u_1} p J inst))
                          P x)
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
                          (@Monoid.toMulOneClass.{u_1} J
                            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))))
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
                          (@Monoid.toMulOneClass.{u_1} J
                            (@DivInvMonoid.toMonoid.{u_1} J (@Group.toDivInvMonoid.{u_1} J inst))))
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
                          @Membership.mem.{u_1, u_1} J (@Sylow.{u_1} p J inst)
                            (@SetLike.instMembership.{u_1, u_1} (@Sylow.{u_1} p J inst) J
                              (@Sylow.instSetLike.{u_1} p J inst))
                            P x)
                        x))
                    n))
                n),
  @Exists.{u_2 + 1} A fun (b : A) =>
    ∀ (x : J),
      @Eq.{u_2 + 1} A (f x)
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
