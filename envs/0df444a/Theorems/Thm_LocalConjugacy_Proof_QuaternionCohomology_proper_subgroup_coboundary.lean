-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_QuaternionCohomology_proper_subgroup_coboundary
-- name    : LocalConjugacy.Proof.QuaternionCohomology.proper_subgroup_coboundary
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:27:07.973897+00:00
-- url     : https://prove2.me/theorems/3242d1bd-e1e0-407e-8ef8-9a13fa467ac5
-- title:
--   Quaternion cocycles vanish on every proper subgroup
-- statement:
--   Let $Q_8=\{\pm1,\pm i,\pm j,\pm k\}$ and let $S=\langle r,s\mid r^3=s^2=1,\ srs=r^{-1}\rangle\cong S_3$. Use the specified action $a:S\to\operatorname{Aut}(Q_8)$ in which $r$ cyclically permutes $i,j,k$ and $s$ sends $(i,j,k)$ to $(-j,-i,-k)$. For any proper subgroup $L<S$ and any cocycle $f:L\to Q_8$ satisfying $f(xy)=f(x)a(x)(f(y))$,
--
--   $$\exists n\in Q_8\;\forall x\in L,\qquad f(x)=n^{-1}a(x)(n).$$
--
--   Thus every cocycle for the restricted action on a proper subgroup is a coboundary. This supplies the local vanishing calculation in the quaternion counterexample.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, QuaternionCohomology.lean, lines 47–90; source SHA-256 11136d53d4ecf66b3c7452da8d2eba6bb1188d212b4a4963d0c18b5b5d8fde02.

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

theorem LocalConjugacy.Proof.QuaternionCohomology.proper_subgroup_coboundary :
∀
  (L :
    @Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
      (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
  (hL :
    @Ne.{1}
      (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
        (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      L
      (@Top.top.{0}
        (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
          (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@Subgroup.instTop.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
          (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
  (f :
    @LocalConjugacy.FiniteCocycle.{0, 0}
      (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
        fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
        @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
          (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
            (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (@SetLike.instMembership.{0, 0}
            (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
            (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          L x)
      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
      (@Subgroup.toGroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
        (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) L)
      (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@MonoidHom.comp.{0, 0, 0}
        (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
          fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
          @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
            (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (@SetLike.instMembership.{0, 0}
              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
              LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
            L x)
        LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
        (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
          (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
            (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
              (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                    (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
        (@MulOneClass.toMulOne.{0}
          (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
            fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
            @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
              (@SetLike.instMembership.{0, 0}
                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
              L x)
          (@Monoid.toMulOneClass.{0}
            (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
              @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (@SetLike.instMembership.{0, 0}
                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                L x)
            (@DivInvMonoid.toMonoid.{0}
              (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  (@SetLike.instMembership.{0, 0}
                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                  L x)
              (@Group.toDivInvMonoid.{0}
                (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                  @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    (@SetLike.instMembership.{0, 0}
                      (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                    L x)
                (@Subgroup.toGroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) L)))))
        (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
          (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))
        (@MulOneClass.toMulOne.{0}
          (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
            (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
              (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                    (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
          (@Monoid.toMulOneClass.{0}
            (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
              (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
            (@DivInvMonoid.toMonoid.{0}
              (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@QuaternionGroup.instGroup
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
              (@Group.toDivInvMonoid.{0}
                (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@QuaternionGroup.instGroup
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                (@MulAut.instGroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@QuaternionGroup.instGroup
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))))))
        LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.action
        (@Subgroup.subtype.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
          (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) L))),
  @Exists.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
    fun (n : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q) =>
    ∀
      (x :
        @Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
          fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
          @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
            (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (@SetLike.instMembership.{0, 0}
              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
              LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
            L x),
      @Eq.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
        (@Subtype.val.{1}
          ((@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
              @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                (@SetLike.instMembership.{0, 0}
                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                L x) →
            LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q)
          (fun
              (f :
                (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                    @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                      (@SetLike.instMembership.{0, 0}
                        (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                        LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                      L x) →
                  LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q) =>
            ∀
              (x y :
                @Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                  @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    (@SetLike.instMembership.{0, 0}
                      (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                    L x),
              @Eq.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                (f
                  (@HMul.hMul.{0, 0, 0}
                    (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                      @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                        (@SetLike.instMembership.{0, 0}
                          (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                        L x)
                    (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                      @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                        (@SetLike.instMembership.{0, 0}
                          (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                        L x)
                    (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                      @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                        (@SetLike.instMembership.{0, 0}
                          (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                        L x)
                    (@instHMul.{0}
                      (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                        @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          (@SetLike.instMembership.{0, 0}
                            (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                          L x)
                      (@MulOne.toMul.{0}
                        (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                          @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            (@SetLike.instMembership.{0, 0}
                              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            L x)
                        (@MulOneClass.toMulOne.{0}
                          (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                            @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              (@SetLike.instMembership.{0, 0}
                                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              L x)
                          (@Monoid.toMulOneClass.{0}
                            (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                              @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                L x)
                            (@DivInvMonoid.toMonoid.{0}
                              (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                                @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@SetLike.instMembership.{0, 0}
                                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  L x)
                              (@Group.toDivInvMonoid.{0}
                                (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                                  @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    (@SetLike.instMembership.{0, 0}
                                      (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                        (@DihedralGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                        (@DihedralGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    L x)
                                (@Subgroup.toGroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                  L)))))))
                    x y))
                (@HMul.hMul.{0, 0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  (@instHMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                    (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@QuaternionGroup.instGroup
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                  (f x)
                  (@DFunLike.coe.{1, 1, 1}
                    (@MulEquiv.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@QuaternionGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                      (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@QuaternionGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                    LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                    (fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q) =>
                      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q)
                    (@EquivLike.toFunLike.{1, 1, 1}
                      (@MulEquiv.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@QuaternionGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                        (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@QuaternionGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      (@MulEquiv.instEquivLike.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                        (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@QuaternionGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                        (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@QuaternionGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
                    (@DFunLike.coe.{1, 1, 1}
                      (@MonoidHom.{0, 0}
                        (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                          @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            (@SetLike.instMembership.{0, 0}
                              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            L x)
                        (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                        (@MulOneClass.toMulOne.{0}
                          (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                            @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              (@SetLike.instMembership.{0, 0}
                                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              L x)
                          (@Monoid.toMulOneClass.{0}
                            (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                              @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                L x)
                            (@DivInvMonoid.toMonoid.{0}
                              (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                                @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@SetLike.instMembership.{0, 0}
                                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  L x)
                              (@Group.toDivInvMonoid.{0}
                                (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                                  @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    (@SetLike.instMembership.{0, 0}
                                      (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                        (@DihedralGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                        (@DihedralGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    L x)
                                (@Subgroup.toGroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                  L)))))
                        (@MulOneClass.toMulOne.{0}
                          (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@QuaternionGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                          (@Monoid.toMulOneClass.{0}
                            (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@QuaternionGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                            (@DivInvMonoid.toMonoid.{0}
                              (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@DivInvMonoid.toMonoid.{0}
                                        LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@Group.toDivInvMonoid.{0}
                                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                          (@QuaternionGroup.instGroup
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                              (@Group.toDivInvMonoid.{0}
                                (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@DivInvMonoid.toMonoid.{0}
                                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                          (@Group.toDivInvMonoid.{0}
                                            LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                                (@MulAut.instGroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@DivInvMonoid.toMonoid.{0}
                                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                          (@Group.toDivInvMonoid.{0}
                                            LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))))))
                      (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                        @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          (@SetLike.instMembership.{0, 0}
                            (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                          L x)
                      (fun
                          (x :
                            @Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                              @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                L x) =>
                        @MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                      (@MonoidHom.instFunLike.{0, 0}
                        (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                          @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            (@SetLike.instMembership.{0, 0}
                              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            L x)
                        (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                        (@MulOneClass.toMulOne.{0}
                          (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                            @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              (@SetLike.instMembership.{0, 0}
                                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              L x)
                          (@Monoid.toMulOneClass.{0}
                            (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                              @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                L x)
                            (@DivInvMonoid.toMonoid.{0}
                              (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                                @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@SetLike.instMembership.{0, 0}
                                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  L x)
                              (@Group.toDivInvMonoid.{0}
                                (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                                  @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    (@SetLike.instMembership.{0, 0}
                                      (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                        (@DihedralGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                        (@DihedralGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    L x)
                                (@Subgroup.toGroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                  L)))))
                        (@MulOneClass.toMulOne.{0}
                          (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@QuaternionGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                          (@Monoid.toMulOneClass.{0}
                            (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@QuaternionGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                            (@DivInvMonoid.toMonoid.{0}
                              (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@DivInvMonoid.toMonoid.{0}
                                        LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@Group.toDivInvMonoid.{0}
                                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                          (@QuaternionGroup.instGroup
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                              (@Group.toDivInvMonoid.{0}
                                (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@DivInvMonoid.toMonoid.{0}
                                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                          (@Group.toDivInvMonoid.{0}
                                            LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                                (@MulAut.instGroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@DivInvMonoid.toMonoid.{0}
                                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                          (@Group.toDivInvMonoid.{0}
                                            LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))))))
                      (@MonoidHom.comp.{0, 0, 0}
                        (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                          @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            (@SetLike.instMembership.{0, 0}
                              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            L x)
                        LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                        (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                          (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                        (@MulOneClass.toMulOne.{0}
                          (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                            @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              (@SetLike.instMembership.{0, 0}
                                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              L x)
                          (@Monoid.toMulOneClass.{0}
                            (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                              @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                L x)
                            (@DivInvMonoid.toMonoid.{0}
                              (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                                @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@DihedralGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@SetLike.instMembership.{0, 0}
                                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  L x)
                              (@Group.toDivInvMonoid.{0}
                                (@Subtype.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                                  @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@DihedralGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    (@SetLike.instMembership.{0, 0}
                                      (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                        (@DihedralGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                      LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                      (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                        (@DihedralGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    L x)
                                (@Subgroup.toGroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                  (@DihedralGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                  L)))))
                        (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                              (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                                (@DihedralGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))))
                        (@MulOneClass.toMulOne.{0}
                          (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                            (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@QuaternionGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                          (@Monoid.toMulOneClass.{0}
                            (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                              (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@QuaternionGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                            (@DivInvMonoid.toMonoid.{0}
                              (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@DivInvMonoid.toMonoid.{0}
                                        LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@Group.toDivInvMonoid.{0}
                                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                          (@QuaternionGroup.instGroup
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                              (@Group.toDivInvMonoid.{0}
                                (@MulAut.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@DivInvMonoid.toMonoid.{0}
                                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                          (@Group.toDivInvMonoid.{0}
                                            LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                                (@MulAut.instGroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                  (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                        (@DivInvMonoid.toMonoid.{0}
                                          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                          (@Group.toDivInvMonoid.{0}
                                            LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))))))
                        LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.action
                        (@Subgroup.subtype.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                          (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) L))
                      x)
                    (f y))))
          f x)
        (@HMul.hMul.{0, 0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
          LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
          (@instHMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
            (@MulOne.toMul.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
              (@MulOneClass.toMulOne.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                (@Monoid.toMulOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                    (@Group.toDivInvMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                      (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
          (@Inv.inv.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
            (@InvOneClass.toInv.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
              (@DivInvOneMonoid.toInvOneClass.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                (@DivisionMonoid.toDivInvOneMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                  (@Group.toDivisionMonoid.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.Q
                    (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
            n)
          (LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.act
            (@Subtype.val.{1} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
              (fun (x : LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S) =>
                @Membership.mem.{0, 0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                  (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  (@SetLike.instMembership.{0, 0}
                    (@Subgroup.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                    (@Subgroup.instSetLike.{0} LocalConjugacy.Proof.LocalConjugacy.QuaternionExample.S
                      (@DihedralGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                  L x)
              x)
            n)) := by sorry
