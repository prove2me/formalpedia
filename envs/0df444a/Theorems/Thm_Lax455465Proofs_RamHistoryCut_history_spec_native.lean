-- Prove2me | Theorems.Thm_Lax455465Proofs_RamHistoryCut_history_spec_native
-- name    : Lax455465Proofs.RamHistoryCut.history_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:26:07.132746+00:00
-- url     : https://prove2.me/theorems/28cdb59b-af1a-48ae-b625-f0fc64af92d3
-- title:
--   Extract a bounded-ratio cut from valid region history
-- statement:
--   Let $I$ be a rational flow instance, $d$ its stored nonnegative rational distance matrix and $\mathcal H$ a valid completed region history of length at most $p>0$. Assume positive total endpoint weight and the complete matrix, radius, score-height and word/buffer guards. The fixed history-cut command outputs an admissible cut $S$ with
--   $$\operatorname{ratio}_I(S)\le\frac{288}{5}\operatorname{steps}(p)\operatorname{metricCost}_I(d).$$
--   It stores the full membership flags of $S$ and meets the source's explicit cost bound depending on $n,|\mathcal H|,M$.
-- source:
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamHistoryCut.lean, theorem Lax455465Proofs.RamHistoryCut.history_spec, line 58

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
namespace Lax455465Proofs.RamHistoryCut
end Lax455465Proofs.RamHistoryCut

theorem Lax455465Proofs.RamHistoryCut.history_spec_native : ∀ (B M : Nat) {n : Nat} (I : Lax455465.RationalEncoding.RationalInstance n) (d : Lax455465Proofs.MetricMatrix.Matrix n)
  (history : List (Lax455465Proofs.RamRegionRecord.Entry n)) (p : Nat),
  @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M →
    @LE.le Nat instLENat
        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@List.length (Lax455465Proofs.RamRegionRecord.Entry n) history))
        M →
      @LT.lt Nat instLTNat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          B →
        @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) B →
          @LT.lt Nat instLTNat
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                (@List.length (Lax455465Proofs.RamRegionRecord.Entry n) history))
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
                (∀ (u w : Fin n), Lax455465Proofs.LpInputSize.Height M (@NNRat.cast Rat Rat.instNNRatCast (d u w))) →
                  (∀ (e : Lax455465Proofs.RamRegionRecord.Entry n),
                      @Membership.mem (Lax455465Proofs.RamRegionRecord.Entry n)
                          (List (Lax455465Proofs.RamRegionRecord.Entry n))
                          (@List.instMembership (Lax455465Proofs.RamRegionRecord.Entry n)) history e →
                        Lax455465Proofs.LpInputSize.Height M
                          (@NNRat.cast Rat Rat.instNNRatCast (@Lax455465Proofs.RamRegionRecord.Entry.radius n e))) →
                    (∀ (S : Finset (Fin n)), @Lax455465Proofs.CutScoreHeight.Bounds n I S M) →
                      @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                          (@Lax455465Proofs.LargeBallRounding.total n I) →
                        @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p →
                          @LE.le Nat instLENat (@List.length (Lax455465Proofs.RamRegionRecord.Entry n) history) p →
                            @Lax455465Proofs.RegionLoop.ValidHistory n I (@Lax455465Proofs.MetricMatrix.rational n d)
                                (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                  (@Lax455465Proofs.RegionRounding.metricCost n I
                                    (@Lax455465Proofs.MetricMatrix.rational n d))
                                  (@Nat.cast Rat Rat.instNatCast p))
                                (@Lax455465Proofs.RegionRounding.radiusBudget n I) p
                                (@Finset.univ (Fin n) (Fin.fintype n))
                                (@List.map (Lax455465Proofs.RamRegionRecord.Entry n)
                                  (Lax455465Proofs.RegionLoop.Region n)
                                  (@Lax455465Proofs.RamRegionRecord.Entry.region n) history) →
                              Lax808846Proofs.Reasoning.Spec B (@Lax455465Proofs.RamHistoryCut.Input n I d history)
                                Lax455465Proofs.RamHistoryCut.command
                                (fun (x τ : Lax808846Proofs.Imp.Env) =>
                                  ∃ (S : Finset (Fin n)),
                                    And (@Lax455465Proofs.CutSweeps.admissibleQ n I S)
                                      (And
                                        (@LE.le Rat Rat.instLE (@Lax455465Proofs.CutSweeps.ratioQ n I S)
                                          (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                            (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                              (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                                                (@OfNat.ofNat Rat (nat_lit 288) (@Rat.instOfNat (nat_lit 288)))
                                                (@OfNat.ofNat Rat (nat_lit 5) (@Rat.instOfNat (nat_lit 5))))
                                              (@Nat.cast Rat Rat.instNatCast (Lax455465Proofs.RegionBudget.steps p)))
                                            (@Lax455465Proofs.RegionRounding.metricCost n I
                                              (@Lax455465Proofs.MetricMatrix.rational n d))))
                                        (Lax455465Proofs.RamVirtualState.Prefix
                                          (Lax455465Proofs.RamUnsignedBuffer.encode
                                            (@Lax455465Proofs.CutScoreData.vertexFlags n S))
                                          "cut.flags" τ)))
                                (Lax455465Proofs.RamHistoryCut.cost n
                                  (@List.length (Lax455465Proofs.RamRegionRecord.Entry n) history) M) := by sorry
