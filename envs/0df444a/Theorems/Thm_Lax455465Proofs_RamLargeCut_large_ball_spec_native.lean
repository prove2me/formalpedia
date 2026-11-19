-- Prove2me | Theorems.Thm_Lax455465Proofs_RamLargeCut_large_ball_spec_native
-- name    : Lax455465Proofs.RamLargeCut.large_ball_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:26:10.493335+00:00
-- url     : https://prove2.me/theorems/9c668908-e6cb-48e4-9427-b1c1a087f001
-- title:
--   Extract a bounded-ratio cut from a large metric ball
-- statement:
--   Let $I$ have positive total endpoint weight and let $d$ be a nonnegative directed metric with zero diagonal and distance separation at least one. Suppose nonempty incoming and outgoing sets each carry at least two-thirds of the total weight and lie within radius $1/(4W^2)$ of their indicated root, where $W$ is that total. Under the complete score, potential, word and buffer bounds, the fixed large-ball command returns an admissible cut $S$ satisfying
--   $$\operatorname{ratio}_I(S)\le6\sum_{u,v}c_{uv}d(u,v).$$
--   Its membership flags are stored and its explicit instruction bound is retained.
-- source:
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamLargeCut.lean, theorem Lax455465Proofs.RamLargeCut.large_ball_spec, line 70

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
namespace Lax455465Proofs.RamLargeCut
end Lax455465Proofs.RamLargeCut

theorem Lax455465Proofs.RamLargeCut.large_ball_spec_native : ∀ (B M : Nat) {n : Nat} (I : Lax455465.RationalEncoding.RationalInstance n) (d : Lax455465Proofs.MetricMatrix.Matrix n)
  (Tin Tout : Finset (Fin n)) (hin : @Finset.Nonempty (Fin n) Tin) (hout : @Finset.Nonempty (Fin n) Tout)
  (root : Fin n),
  @Lax455465Proofs.LargePotentialData.Bounds n I d Tin Tout hin hout M →
    (∀ (S : Finset (Fin n)), @Lax455465Proofs.CutScoreHeight.Bounds n I S M) →
      @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M →
        @LT.lt Nat instLTNat
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            B →
          @LT.lt Nat instLTNat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              B →
            @LT.lt Nat instLTNat
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                B →
              @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                  (@Lax455465Proofs.LargeBallRounding.total n I) →
                (∀ (v : Fin n),
                    @Eq NNRat (d v v)
                      (@OfNat.ofNat NNRat (nat_lit 0)
                        (@Zero.toOfNat0 NNRat
                          (@MulZeroClass.toZero NNRat
                            (@instMulZeroClassOfSemiring NNRat
                              (@DivisionSemiring.toSemiring NNRat
                                (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))) →
                  @LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                      (@Lax455465Proofs.LargeBallRounding.distanceSeparation n I
                        (@Lax455465Proofs.MetricMatrix.rational n d)) →
                    (∀ (u v w : Fin n),
                        @LE.le Rat Rat.instLE (@NNRat.cast Rat Rat.instNNRatCast (d u w))
                          (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd)
                            (@NNRat.cast Rat Rat.instNNRatCast (d u v)) (@NNRat.cast Rat Rat.instNNRatCast (d v w)))) →
                      (∀ (s : Fin n),
                          @Membership.mem (Fin n) (Finset (Fin n))
                              (@SetLike.instMembership (Finset (Fin n)) (Fin n) (@Finset.instSetLike (Fin n))) Tin s →
                            @LE.le Rat Rat.instLE (@NNRat.cast Rat Rat.instNNRatCast (d s root))
                              (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                  (@OfNat.ofNat Rat (nat_lit 4) (@Rat.instOfNat (nat_lit 4)))
                                  (@HPow.hPow Rat Nat Rat
                                    (@instHPow Rat Nat (@NPow.toPow Rat (@Monoid.toNPow Rat Rat.monoid)))
                                    (@Lax455465Proofs.LargeBallRounding.total n I)
                                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) →
                        (∀ (t : Fin n),
                            @Membership.mem (Fin n) (Finset (Fin n))
                                (@SetLike.instMembership (Finset (Fin n)) (Fin n) (@Finset.instSetLike (Fin n))) Tout
                                t →
                              @LE.le Rat Rat.instLE (@NNRat.cast Rat Rat.instNNRatCast (d root t))
                                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                  (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                                  (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                    (@OfNat.ofNat Rat (nat_lit 4) (@Rat.instOfNat (nat_lit 4)))
                                    (@HPow.hPow Rat Nat Rat
                                      (@instHPow Rat Nat (@NPow.toPow Rat (@Monoid.toNPow Rat Rat.monoid)))
                                      (@Lax455465Proofs.LargeBallRounding.total n I)
                                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))) →
                          @LE.le Rat Rat.instLE
                              (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                  (@OfNat.ofNat Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                                  (@OfNat.ofNat Rat (nat_lit 3) (@Rat.instOfNat (nat_lit 3))))
                                (@Lax455465Proofs.LargeBallRounding.total n I))
                              (@Lax455465Proofs.LargeBallRounding.mass n I Tin) →
                            @LE.le Rat Rat.instLE
                                (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                  (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                    (@OfNat.ofNat Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
                                    (@OfNat.ofNat Rat (nat_lit 3) (@Rat.instOfNat (nat_lit 3))))
                                  (@Lax455465Proofs.LargeBallRounding.total n I))
                                (@Lax455465Proofs.LargeBallRounding.mass n I Tout) →
                              Lax808846Proofs.Reasoning.Spec B (@Lax455465Proofs.RamLargeCut.Input n I d Tin Tout)
                                Lax455465Proofs.RamLargeCut.command
                                (fun (x τ : Lax808846Proofs.Imp.Env) =>
                                  ∃ (S : Finset (Fin n)),
                                    And (@Lax455465Proofs.CutSweeps.admissibleQ n I S)
                                      (And
                                        (@LE.le Rat Rat.instLE (@Lax455465Proofs.CutSweeps.ratioQ n I S)
                                          (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                            (@OfNat.ofNat Rat (nat_lit 6) (@Rat.instOfNat (nat_lit 6)))
                                            (∑ u : Fin n,
                                              ∑ v : Fin n,
                                                @HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                                  (@NNRat.cast Rat Rat.instNNRatCast
                                                    (@Lax455465.RationalEncoding.RationalInstance.capacity n I u v))
                                                  (@NNRat.cast Rat Rat.instNNRatCast (d u v)))))
                                        (Lax455465Proofs.RamVirtualState.Prefix
                                          (Lax455465Proofs.RamUnsignedBuffer.encode
                                            (@Lax455465Proofs.CutScoreData.vertexFlags n S))
                                          "cut.flags" τ)))
                                (Lax455465Proofs.RamLargeCut.cost n M) := by sorry
