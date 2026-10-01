-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_quaternion_sylow_coboundary
-- name    : LocalConjugacy.Proof.quaternion_sylow_coboundary
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:27:42.348463+00:00
-- url     : https://prove2.me/theorems/bc84d2a5-a0e4-4358-9212-003910b6c4b7
-- title:
--   Sylow cocycles for the quaternion action are coboundaries
-- statement:
--   Let $Q_8=\{\pm1,\pm i,\pm j,\pm k\}$ be the quaternion group and let $a:S_3\to\operatorname{Aut}(Q_8)$ be the specified quaternion action, presented by an order-three generator rotating $i,j,k$ and an order-two generator sending $(i,j,k)$ to $(-j,-i,-k)$. Let $p$ be any prime, let $P$ be a Sylow $p$-subgroup of $S_3$, and let $f:P\to Q_8$ satisfy $f(xy)=f(x)a(x)(f(y))$. Then
--
--   $$\exists n\in Q_8,\quad\forall x\in P,\qquad f(x)=n^{-1}a(x)(n).$$
--
--   Thus the first nonabelian cohomology of every Sylow subgroup for this action is trivial. This verifies the local cohomology vanishing used in the quaternion example.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, QuaternionAction.lean, lines 58–97; source SHA-256 61f51a7fad9a267340e20e251d0e1252e2a5a60fa785bab4726aa027181e59ac.

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

theorem LocalConjugacy.Proof.quaternion_sylow_coboundary :
∀ (p : Nat) (hp : Nat.Prime p)
  (P :
    @Sylow.{0} p LocalConjugacy.S3
      (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
  (f :
    @LocalConjugacy.FiniteCocycle.{0, 0}
      (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
        @Membership.mem.{0, 0} LocalConjugacy.S3
          (@Subgroup.{0} LocalConjugacy.S3
            (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
          (@SetLike.instMembership.{0, 0}
            (@Subgroup.{0} LocalConjugacy.S3
              (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
            LocalConjugacy.S3
            (@Subgroup.instSetLike.{0} LocalConjugacy.S3
              (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
          (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
            (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) P)
          x)
      LocalConjugacy.Q8
      (@Subgroup.toGroup.{0} LocalConjugacy.S3
        (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
        (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
          (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) P))
      (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@MonoidHom.comp.{0, 0, 0}
        (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
          @Membership.mem.{0, 0} LocalConjugacy.S3
            (@Subgroup.{0} LocalConjugacy.S3
              (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
            (@SetLike.instMembership.{0, 0}
              (@Subgroup.{0} LocalConjugacy.S3
                (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
              LocalConjugacy.S3
              (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
            (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
              (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) P)
            x)
        LocalConjugacy.S3
        (@MulAut.{0} LocalConjugacy.Q8
          (@MulOne.toMul.{0} LocalConjugacy.Q8
            (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
              (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                    (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
        (@MulOneClass.toMulOne.{0}
          (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
            @Membership.mem.{0, 0} LocalConjugacy.S3
              (@Subgroup.{0} LocalConjugacy.S3
                (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
              (@SetLike.instMembership.{0, 0}
                (@Subgroup.{0} LocalConjugacy.S3
                  (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                LocalConjugacy.S3
                (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                  (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
              (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) P)
              x)
          (@Monoid.toMulOneClass.{0}
            (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
              @Membership.mem.{0, 0} LocalConjugacy.S3
                (@Subgroup.{0} LocalConjugacy.S3
                  (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                (@SetLike.instMembership.{0, 0}
                  (@Subgroup.{0} LocalConjugacy.S3
                    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                  LocalConjugacy.S3
                  (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                  (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) P)
                x)
            (@DivInvMonoid.toMonoid.{0}
              (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                @Membership.mem.{0, 0} LocalConjugacy.S3
                  (@Subgroup.{0} LocalConjugacy.S3
                    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                  (@SetLike.instMembership.{0, 0}
                    (@Subgroup.{0} LocalConjugacy.S3
                      (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                    LocalConjugacy.S3
                    (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                      (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) P)
                  x)
              (@Group.toDivInvMonoid.{0}
                (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                  @Membership.mem.{0, 0} LocalConjugacy.S3
                    (@Subgroup.{0} LocalConjugacy.S3
                      (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                    (@SetLike.instMembership.{0, 0}
                      (@Subgroup.{0} LocalConjugacy.S3
                        (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                      LocalConjugacy.S3
                      (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                        (@Equiv.Perm.permGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                    (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                      (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) P)
                    x)
                (@Subgroup.toGroup.{0} LocalConjugacy.S3
                  (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                    P))))))
        (@MulOneClass.toMulOne.{0} LocalConjugacy.S3
          (@Monoid.toMulOneClass.{0} LocalConjugacy.S3
            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.S3
              (@Group.toDivInvMonoid.{0} LocalConjugacy.S3
                (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
        (@MulOneClass.toMulOne.{0}
          (@MulAut.{0} LocalConjugacy.Q8
            (@MulOne.toMul.{0} LocalConjugacy.Q8
              (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                  (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                    (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                      (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
          (@Monoid.toMulOneClass.{0}
            (@MulAut.{0} LocalConjugacy.Q8
              (@MulOne.toMul.{0} LocalConjugacy.Q8
                (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                        (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
            (@DivInvMonoid.toMonoid.{0}
              (@MulAut.{0} LocalConjugacy.Q8
                (@MulOne.toMul.{0} LocalConjugacy.Q8
                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                      (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                        (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                          (@QuaternionGroup.instGroup
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
              (@Group.toDivInvMonoid.{0}
                (@MulAut.{0} LocalConjugacy.Q8
                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                            (@QuaternionGroup.instGroup
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                (@MulAut.instGroup.{0} LocalConjugacy.Q8
                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                            (@QuaternionGroup.instGroup
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))))))
        LocalConjugacy.Proof.quaternionAction
        (@Subgroup.subtype.{0} LocalConjugacy.S3
          (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
          (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
            (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) P)))),
  @Exists.{1} LocalConjugacy.Q8 fun (n : LocalConjugacy.Q8) =>
    ∀
      (x :
        @Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
          @Membership.mem.{0, 0} LocalConjugacy.S3
            (@Sylow.{0} p LocalConjugacy.S3
              (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
            (@SetLike.instMembership.{0, 0}
              (@Sylow.{0} p LocalConjugacy.S3
                (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
              LocalConjugacy.S3
              (@Sylow.instSetLike.{0} p LocalConjugacy.S3
                (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
            P x),
      @Eq.{1} LocalConjugacy.Q8
        (@Subtype.val.{1}
          ((@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
              @Membership.mem.{0, 0} LocalConjugacy.S3
                (@Subgroup.{0} LocalConjugacy.S3
                  (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                (@SetLike.instMembership.{0, 0}
                  (@Subgroup.{0} LocalConjugacy.S3
                    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                  LocalConjugacy.S3
                  (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                    (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                  (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) P)
                x) →
            LocalConjugacy.Q8)
          (fun
              (f :
                (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                    @Membership.mem.{0, 0} LocalConjugacy.S3
                      (@Subgroup.{0} LocalConjugacy.S3
                        (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                      (@SetLike.instMembership.{0, 0}
                        (@Subgroup.{0} LocalConjugacy.S3
                          (@Equiv.Perm.permGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                        LocalConjugacy.S3
                        (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                          (@Equiv.Perm.permGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                      (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                        (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                        P)
                      x) →
                  LocalConjugacy.Q8) =>
            ∀
              (x y :
                @Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                  @Membership.mem.{0, 0} LocalConjugacy.S3
                    (@Subgroup.{0} LocalConjugacy.S3
                      (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                    (@SetLike.instMembership.{0, 0}
                      (@Subgroup.{0} LocalConjugacy.S3
                        (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                      LocalConjugacy.S3
                      (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                        (@Equiv.Perm.permGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                    (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                      (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) P)
                    x),
              @Eq.{1} LocalConjugacy.Q8
                (f
                  (@HMul.hMul.{0, 0, 0}
                    (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                      @Membership.mem.{0, 0} LocalConjugacy.S3
                        (@Subgroup.{0} LocalConjugacy.S3
                          (@Equiv.Perm.permGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                        (@SetLike.instMembership.{0, 0}
                          (@Subgroup.{0} LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                          LocalConjugacy.S3
                          (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                        (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                          (@Equiv.Perm.permGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          P)
                        x)
                    (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                      @Membership.mem.{0, 0} LocalConjugacy.S3
                        (@Subgroup.{0} LocalConjugacy.S3
                          (@Equiv.Perm.permGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                        (@SetLike.instMembership.{0, 0}
                          (@Subgroup.{0} LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                          LocalConjugacy.S3
                          (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                        (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                          (@Equiv.Perm.permGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          P)
                        x)
                    (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                      @Membership.mem.{0, 0} LocalConjugacy.S3
                        (@Subgroup.{0} LocalConjugacy.S3
                          (@Equiv.Perm.permGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                        (@SetLike.instMembership.{0, 0}
                          (@Subgroup.{0} LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                          LocalConjugacy.S3
                          (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                        (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                          (@Equiv.Perm.permGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          P)
                        x)
                    (@instHMul.{0}
                      (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                        @Membership.mem.{0, 0} LocalConjugacy.S3
                          (@Subgroup.{0} LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                          (@SetLike.instMembership.{0, 0}
                            (@Subgroup.{0} LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            LocalConjugacy.S3
                            (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                          (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            P)
                          x)
                      (@MulOne.toMul.{0}
                        (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                          @Membership.mem.{0, 0} LocalConjugacy.S3
                            (@Subgroup.{0} LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            (@SetLike.instMembership.{0, 0}
                              (@Subgroup.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              LocalConjugacy.S3
                              (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                            (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              P)
                            x)
                        (@MulOneClass.toMulOne.{0}
                          (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                            @Membership.mem.{0, 0} LocalConjugacy.S3
                              (@Subgroup.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              (@SetLike.instMembership.{0, 0}
                                (@Subgroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                LocalConjugacy.S3
                                (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                              (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                P)
                              x)
                          (@Monoid.toMulOneClass.{0}
                            (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                              @Membership.mem.{0, 0} LocalConjugacy.S3
                                (@Subgroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  LocalConjugacy.S3
                                  (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  P)
                                x)
                            (@DivInvMonoid.toMonoid.{0}
                              (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                                @Membership.mem.{0, 0} LocalConjugacy.S3
                                  (@Subgroup.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  (@SetLike.instMembership.{0, 0}
                                    (@Subgroup.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    LocalConjugacy.S3
                                    (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    P)
                                  x)
                              (@Group.toDivInvMonoid.{0}
                                (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                                  @Membership.mem.{0, 0} LocalConjugacy.S3
                                    (@Subgroup.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    (@SetLike.instMembership.{0, 0}
                                      (@Subgroup.{0} LocalConjugacy.S3
                                        (@Equiv.Perm.permGroup.{0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                      LocalConjugacy.S3
                                      (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                        (@Equiv.Perm.permGroup.{0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                    (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                      P)
                                    x)
                                (@Subgroup.toGroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    P))))))))
                    x y))
                (@HMul.hMul.{0, 0, 0} LocalConjugacy.Q8 LocalConjugacy.Q8 LocalConjugacy.Q8
                  (@instHMul.{0} LocalConjugacy.Q8
                    (@MulOne.toMul.{0} LocalConjugacy.Q8
                      (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                        (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                          (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                            (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                              (@QuaternionGroup.instGroup
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                  (f x)
                  (@DFunLike.coe.{1, 1, 1}
                    (@MulEquiv.{0, 0} LocalConjugacy.Q8 LocalConjugacy.Q8
                      (@MulOne.toMul.{0} LocalConjugacy.Q8
                        (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                          (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                              (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                (@QuaternionGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                      (@MulOne.toMul.{0} LocalConjugacy.Q8
                        (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                          (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                              (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                (@QuaternionGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                    LocalConjugacy.Q8 (fun (x : LocalConjugacy.Q8) => LocalConjugacy.Q8)
                    (@EquivLike.toFunLike.{1, 1, 1}
                      (@MulEquiv.{0, 0} LocalConjugacy.Q8 LocalConjugacy.Q8
                        (@MulOne.toMul.{0} LocalConjugacy.Q8
                          (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                            (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                              (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                  (@QuaternionGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                        (@MulOne.toMul.{0} LocalConjugacy.Q8
                          (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                            (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                              (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                  (@QuaternionGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                      LocalConjugacy.Q8 LocalConjugacy.Q8
                      (@MulEquiv.instEquivLike.{0, 0} LocalConjugacy.Q8 LocalConjugacy.Q8
                        (@MulOne.toMul.{0} LocalConjugacy.Q8
                          (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                            (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                              (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                  (@QuaternionGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                        (@MulOne.toMul.{0} LocalConjugacy.Q8
                          (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                            (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                              (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                  (@QuaternionGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
                    (@DFunLike.coe.{1, 1, 1}
                      (@MonoidHom.{0, 0}
                        (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                          @Membership.mem.{0, 0} LocalConjugacy.S3
                            (@Subgroup.{0} LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            (@SetLike.instMembership.{0, 0}
                              (@Subgroup.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              LocalConjugacy.S3
                              (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                            (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              P)
                            x)
                        (@MulAut.{0} LocalConjugacy.Q8
                          (@MulOne.toMul.{0} LocalConjugacy.Q8
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                        (@MulOneClass.toMulOne.{0}
                          (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                            @Membership.mem.{0, 0} LocalConjugacy.S3
                              (@Subgroup.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              (@SetLike.instMembership.{0, 0}
                                (@Subgroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                LocalConjugacy.S3
                                (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                              (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                P)
                              x)
                          (@Monoid.toMulOneClass.{0}
                            (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                              @Membership.mem.{0, 0} LocalConjugacy.S3
                                (@Subgroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  LocalConjugacy.S3
                                  (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  P)
                                x)
                            (@DivInvMonoid.toMonoid.{0}
                              (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                                @Membership.mem.{0, 0} LocalConjugacy.S3
                                  (@Subgroup.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  (@SetLike.instMembership.{0, 0}
                                    (@Subgroup.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    LocalConjugacy.S3
                                    (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    P)
                                  x)
                              (@Group.toDivInvMonoid.{0}
                                (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                                  @Membership.mem.{0, 0} LocalConjugacy.S3
                                    (@Subgroup.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    (@SetLike.instMembership.{0, 0}
                                      (@Subgroup.{0} LocalConjugacy.S3
                                        (@Equiv.Perm.permGroup.{0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                      LocalConjugacy.S3
                                      (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                        (@Equiv.Perm.permGroup.{0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                    (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                      P)
                                    x)
                                (@Subgroup.toGroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    P))))))
                        (@MulOneClass.toMulOne.{0}
                          (@MulAut.{0} LocalConjugacy.Q8
                            (@MulOne.toMul.{0} LocalConjugacy.Q8
                              (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                  (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                    (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                      (@QuaternionGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                          (@Monoid.toMulOneClass.{0}
                            (@MulAut.{0} LocalConjugacy.Q8
                              (@MulOne.toMul.{0} LocalConjugacy.Q8
                                (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                        (@QuaternionGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                            (@DivInvMonoid.toMonoid.{0}
                              (@MulAut.{0} LocalConjugacy.Q8
                                (@MulOne.toMul.{0} LocalConjugacy.Q8
                                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                      (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                        (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                          (@QuaternionGroup.instGroup
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                              (@Group.toDivInvMonoid.{0}
                                (@MulAut.{0} LocalConjugacy.Q8
                                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                                (@MulAut.instGroup.{0} LocalConjugacy.Q8
                                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))))))
                      (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                        @Membership.mem.{0, 0} LocalConjugacy.S3
                          (@Subgroup.{0} LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                          (@SetLike.instMembership.{0, 0}
                            (@Subgroup.{0} LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            LocalConjugacy.S3
                            (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                          (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            P)
                          x)
                      (fun
                          (x :
                            @Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                              @Membership.mem.{0, 0} LocalConjugacy.S3
                                (@Subgroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  LocalConjugacy.S3
                                  (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  P)
                                x) =>
                        @MulAut.{0} LocalConjugacy.Q8
                          (@MulOne.toMul.{0} LocalConjugacy.Q8
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                      (@MonoidHom.instFunLike.{0, 0}
                        (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                          @Membership.mem.{0, 0} LocalConjugacy.S3
                            (@Subgroup.{0} LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            (@SetLike.instMembership.{0, 0}
                              (@Subgroup.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              LocalConjugacy.S3
                              (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                            (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              P)
                            x)
                        (@MulAut.{0} LocalConjugacy.Q8
                          (@MulOne.toMul.{0} LocalConjugacy.Q8
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                        (@MulOneClass.toMulOne.{0}
                          (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                            @Membership.mem.{0, 0} LocalConjugacy.S3
                              (@Subgroup.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              (@SetLike.instMembership.{0, 0}
                                (@Subgroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                LocalConjugacy.S3
                                (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                              (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                P)
                              x)
                          (@Monoid.toMulOneClass.{0}
                            (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                              @Membership.mem.{0, 0} LocalConjugacy.S3
                                (@Subgroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  LocalConjugacy.S3
                                  (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  P)
                                x)
                            (@DivInvMonoid.toMonoid.{0}
                              (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                                @Membership.mem.{0, 0} LocalConjugacy.S3
                                  (@Subgroup.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  (@SetLike.instMembership.{0, 0}
                                    (@Subgroup.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    LocalConjugacy.S3
                                    (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    P)
                                  x)
                              (@Group.toDivInvMonoid.{0}
                                (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                                  @Membership.mem.{0, 0} LocalConjugacy.S3
                                    (@Subgroup.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    (@SetLike.instMembership.{0, 0}
                                      (@Subgroup.{0} LocalConjugacy.S3
                                        (@Equiv.Perm.permGroup.{0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                      LocalConjugacy.S3
                                      (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                        (@Equiv.Perm.permGroup.{0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                    (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                      P)
                                    x)
                                (@Subgroup.toGroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    P))))))
                        (@MulOneClass.toMulOne.{0}
                          (@MulAut.{0} LocalConjugacy.Q8
                            (@MulOne.toMul.{0} LocalConjugacy.Q8
                              (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                  (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                    (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                      (@QuaternionGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                          (@Monoid.toMulOneClass.{0}
                            (@MulAut.{0} LocalConjugacy.Q8
                              (@MulOne.toMul.{0} LocalConjugacy.Q8
                                (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                        (@QuaternionGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                            (@DivInvMonoid.toMonoid.{0}
                              (@MulAut.{0} LocalConjugacy.Q8
                                (@MulOne.toMul.{0} LocalConjugacy.Q8
                                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                      (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                        (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                          (@QuaternionGroup.instGroup
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                              (@Group.toDivInvMonoid.{0}
                                (@MulAut.{0} LocalConjugacy.Q8
                                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                                (@MulAut.instGroup.{0} LocalConjugacy.Q8
                                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))))))
                      (@MonoidHom.comp.{0, 0, 0}
                        (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                          @Membership.mem.{0, 0} LocalConjugacy.S3
                            (@Subgroup.{0} LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                            (@SetLike.instMembership.{0, 0}
                              (@Subgroup.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              LocalConjugacy.S3
                              (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                            (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                              (@Equiv.Perm.permGroup.{0}
                                (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                              P)
                            x)
                        LocalConjugacy.S3
                        (@MulAut.{0} LocalConjugacy.Q8
                          (@MulOne.toMul.{0} LocalConjugacy.Q8
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                        (@MulOneClass.toMulOne.{0}
                          (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                            @Membership.mem.{0, 0} LocalConjugacy.S3
                              (@Subgroup.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                              (@SetLike.instMembership.{0, 0}
                                (@Subgroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                LocalConjugacy.S3
                                (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                              (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                P)
                              x)
                          (@Monoid.toMulOneClass.{0}
                            (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                              @Membership.mem.{0, 0} LocalConjugacy.S3
                                (@Subgroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                (@SetLike.instMembership.{0, 0}
                                  (@Subgroup.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  LocalConjugacy.S3
                                  (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  P)
                                x)
                            (@DivInvMonoid.toMonoid.{0}
                              (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                                @Membership.mem.{0, 0} LocalConjugacy.S3
                                  (@Subgroup.{0} LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                  (@SetLike.instMembership.{0, 0}
                                    (@Subgroup.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    LocalConjugacy.S3
                                    (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    P)
                                  x)
                              (@Group.toDivInvMonoid.{0}
                                (@Subtype.{1} LocalConjugacy.S3 fun (x : LocalConjugacy.S3) =>
                                  @Membership.mem.{0, 0} LocalConjugacy.S3
                                    (@Subgroup.{0} LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                    (@SetLike.instMembership.{0, 0}
                                      (@Subgroup.{0} LocalConjugacy.S3
                                        (@Equiv.Perm.permGroup.{0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                                      LocalConjugacy.S3
                                      (@Subgroup.instSetLike.{0} LocalConjugacy.S3
                                        (@Equiv.Perm.permGroup.{0}
                                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                                    (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                      (@Equiv.Perm.permGroup.{0}
                                        (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                      P)
                                    x)
                                (@Subgroup.toGroup.{0} LocalConjugacy.S3
                                  (@Equiv.Perm.permGroup.{0}
                                    (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                  (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                                    (@Equiv.Perm.permGroup.{0}
                                      (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                                    P))))))
                        (@MulOneClass.toMulOne.{0} LocalConjugacy.S3
                          (@Monoid.toMulOneClass.{0} LocalConjugacy.S3
                            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.S3
                              (@Group.toDivInvMonoid.{0} LocalConjugacy.S3
                                (@Equiv.Perm.permGroup.{0}
                                  (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
                        (@MulOneClass.toMulOne.{0}
                          (@MulAut.{0} LocalConjugacy.Q8
                            (@MulOne.toMul.{0} LocalConjugacy.Q8
                              (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                  (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                    (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                      (@QuaternionGroup.instGroup
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                          (@Monoid.toMulOneClass.{0}
                            (@MulAut.{0} LocalConjugacy.Q8
                              (@MulOne.toMul.{0} LocalConjugacy.Q8
                                (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                        (@QuaternionGroup.instGroup
                                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                            (@DivInvMonoid.toMonoid.{0}
                              (@MulAut.{0} LocalConjugacy.Q8
                                (@MulOne.toMul.{0} LocalConjugacy.Q8
                                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                      (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                        (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                          (@QuaternionGroup.instGroup
                                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                              (@Group.toDivInvMonoid.{0}
                                (@MulAut.{0} LocalConjugacy.Q8
                                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                                (@MulAut.instGroup.{0} LocalConjugacy.Q8
                                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                            (@QuaternionGroup.instGroup
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))))))
                        LocalConjugacy.Proof.quaternionAction
                        (@Subgroup.subtype.{0} LocalConjugacy.S3
                          (@Equiv.Perm.permGroup.{0}
                            (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                          (@Sylow.toSubgroup.{0} p LocalConjugacy.S3
                            (@Equiv.Perm.permGroup.{0}
                              (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
                            P)))
                      x)
                    (f y))))
          f x)
        (@HMul.hMul.{0, 0, 0} LocalConjugacy.Q8 LocalConjugacy.Q8 LocalConjugacy.Q8
          (@instHMul.{0} LocalConjugacy.Q8
            (@MulOne.toMul.{0} LocalConjugacy.Q8
              (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                  (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                    (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                      (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
          (@Inv.inv.{0} LocalConjugacy.Q8
            (@InvOneClass.toInv.{0} LocalConjugacy.Q8
              (@DivInvOneMonoid.toInvOneClass.{0} LocalConjugacy.Q8
                (@DivisionMonoid.toDivInvOneMonoid.{0} LocalConjugacy.Q8
                  (@Group.toDivisionMonoid.{0} LocalConjugacy.Q8
                    (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
            n)
          (@DFunLike.coe.{1, 1, 1}
            (@MulEquiv.{0, 0} LocalConjugacy.Q8 LocalConjugacy.Q8
              (@MulOne.toMul.{0} LocalConjugacy.Q8
                (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                        (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
              (@MulOne.toMul.{0} LocalConjugacy.Q8
                (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                  (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                      (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                        (@QuaternionGroup.instGroup (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
            LocalConjugacy.Q8 (fun (x : LocalConjugacy.Q8) => LocalConjugacy.Q8)
            (@EquivLike.toFunLike.{1, 1, 1}
              (@MulEquiv.{0, 0} LocalConjugacy.Q8 LocalConjugacy.Q8
                (@MulOne.toMul.{0} LocalConjugacy.Q8
                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                      (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                        (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                          (@QuaternionGroup.instGroup
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                (@MulOne.toMul.{0} LocalConjugacy.Q8
                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                      (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                        (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                          (@QuaternionGroup.instGroup
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
              LocalConjugacy.Q8 LocalConjugacy.Q8
              (@MulEquiv.instEquivLike.{0, 0} LocalConjugacy.Q8 LocalConjugacy.Q8
                (@MulOne.toMul.{0} LocalConjugacy.Q8
                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                      (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                        (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                          (@QuaternionGroup.instGroup
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                (@MulOne.toMul.{0} LocalConjugacy.Q8
                  (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                    (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                      (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                        (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                          (@QuaternionGroup.instGroup
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))
            (@DFunLike.coe.{1, 1, 1}
              (@MonoidHom.{0, 0} LocalConjugacy.S3
                (@MulAut.{0} LocalConjugacy.Q8
                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                            (@QuaternionGroup.instGroup
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                (@MulOneClass.toMulOne.{0} LocalConjugacy.S3
                  (@Monoid.toMulOneClass.{0} LocalConjugacy.S3
                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.S3
                      (@Group.toDivInvMonoid.{0} LocalConjugacy.S3
                        (@Equiv.Perm.permGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
                (@MulOneClass.toMulOne.{0}
                  (@MulAut.{0} LocalConjugacy.Q8
                    (@MulOne.toMul.{0} LocalConjugacy.Q8
                      (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                        (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                          (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                            (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                              (@QuaternionGroup.instGroup
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                  (@Monoid.toMulOneClass.{0}
                    (@MulAut.{0} LocalConjugacy.Q8
                      (@MulOne.toMul.{0} LocalConjugacy.Q8
                        (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                          (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                              (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                (@QuaternionGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                    (@DivInvMonoid.toMonoid.{0}
                      (@MulAut.{0} LocalConjugacy.Q8
                        (@MulOne.toMul.{0} LocalConjugacy.Q8
                          (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                            (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                              (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                  (@QuaternionGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                      (@Group.toDivInvMonoid.{0}
                        (@MulAut.{0} LocalConjugacy.Q8
                          (@MulOne.toMul.{0} LocalConjugacy.Q8
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                        (@MulAut.instGroup.{0} LocalConjugacy.Q8
                          (@MulOne.toMul.{0} LocalConjugacy.Q8
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))))))
              LocalConjugacy.S3
              (fun (x : LocalConjugacy.S3) =>
                @MulAut.{0} LocalConjugacy.Q8
                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                            (@QuaternionGroup.instGroup
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
              (@MonoidHom.instFunLike.{0, 0} LocalConjugacy.S3
                (@MulAut.{0} LocalConjugacy.Q8
                  (@MulOne.toMul.{0} LocalConjugacy.Q8
                    (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                      (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                        (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                          (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                            (@QuaternionGroup.instGroup
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                (@MulOneClass.toMulOne.{0} LocalConjugacy.S3
                  (@Monoid.toMulOneClass.{0} LocalConjugacy.S3
                    (@DivInvMonoid.toMonoid.{0} LocalConjugacy.S3
                      (@Group.toDivInvMonoid.{0} LocalConjugacy.S3
                        (@Equiv.Perm.permGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))))
                (@MulOneClass.toMulOne.{0}
                  (@MulAut.{0} LocalConjugacy.Q8
                    (@MulOne.toMul.{0} LocalConjugacy.Q8
                      (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                        (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                          (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                            (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                              (@QuaternionGroup.instGroup
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                  (@Monoid.toMulOneClass.{0}
                    (@MulAut.{0} LocalConjugacy.Q8
                      (@MulOne.toMul.{0} LocalConjugacy.Q8
                        (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                          (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                            (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                              (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                (@QuaternionGroup.instGroup
                                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                    (@DivInvMonoid.toMonoid.{0}
                      (@MulAut.{0} LocalConjugacy.Q8
                        (@MulOne.toMul.{0} LocalConjugacy.Q8
                          (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                            (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                              (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                  (@QuaternionGroup.instGroup
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                      (@Group.toDivInvMonoid.{0}
                        (@MulAut.{0} LocalConjugacy.Q8
                          (@MulOne.toMul.{0} LocalConjugacy.Q8
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))))
                        (@MulAut.instGroup.{0} LocalConjugacy.Q8
                          (@MulOne.toMul.{0} LocalConjugacy.Q8
                            (@MulOneClass.toMulOne.{0} LocalConjugacy.Q8
                              (@Monoid.toMulOneClass.{0} LocalConjugacy.Q8
                                (@DivInvMonoid.toMonoid.{0} LocalConjugacy.Q8
                                  (@Group.toDivInvMonoid.{0} LocalConjugacy.Q8
                                    (@QuaternionGroup.instGroup
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))))))))
              LocalConjugacy.Proof.quaternionAction
              (@Subtype.val.{1} LocalConjugacy.S3
                (fun (x : LocalConjugacy.S3) =>
                  @Membership.mem.{0, 0} LocalConjugacy.S3
                    (@Sylow.{0} p LocalConjugacy.S3
                      (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                    (@SetLike.instMembership.{0, 0}
                      (@Sylow.{0} p LocalConjugacy.S3
                        (@Equiv.Perm.permGroup.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
                      LocalConjugacy.S3
                      (@Sylow.instSetLike.{0} p LocalConjugacy.S3
                        (@Equiv.Perm.permGroup.{0}
                          (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))))
                    P x)
                x))
            n)) := by sorry
