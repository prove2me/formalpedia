-- Prove2me | Theorems.Thm_Lax455465Proofs_RamRegionBoundedLoop_command_spec_native
-- name    : Lax455465Proofs.RamRegionBoundedLoop.command_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:33.113204+00:00
-- url     : https://prove2.me/theorems/55c8ac16-51c7-4ffc-b1f4-8bd53e91b010
-- title:
--   Bounded native region-growth loop
-- statement:
--   Fix a rational network instance, its rational metric, the seed and threshold data, and the active-set/history state appearing in this interface. Assume its complete coefficient-height, dimension, positivity, word-size and allocated-storage guards. The fixed command implements the complete bounded region-growth process, with the explicit instruction bound from the source:
--
--   $$\mathrm{Spec}_B(\mathrm{InitialRegion},c_{\rm loop},\mathrm{FinalRegion},T_{\rm loop}).$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamRegionBoundedLoop.lean, theorem command_spec (lines 15–49)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax455465Proofs.RamRegionBoundedLoop
end Lax455465Proofs.RamRegionBoundedLoop

theorem Lax455465Proofs.RamRegionBoundedLoop.command_spec_native : ∀ (B M H : Nat) {n : Nat} (I : Lax455465.RationalEncoding.RationalInstance n)
  (length : Lax455465Proofs.MetricMatrix.Matrix n) (seed beta delta threshold : NNRat) (p : Nat),
  @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M →
    @LE.le Nat instLENat (Lax455465Proofs.RegionBudget.steps p) M →
      @LT.lt Nat instLTNat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          B →
        @LT.lt Nat instLTNat
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H)
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
              @LT.lt Nat instLTNat
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (Lax455465Proofs.RegionBudget.steps p)
                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n)))
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  B →
                @LT.lt Nat instLTNat
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) p)
                      (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                    B →
                  Lax455465Proofs.LpInputSize.Height
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) H)
                      (@NNRat.cast Rat Rat.instNNRatCast threshold) →
                    (∀ (v : Fin n),
                        @LE.le Nat instLENat (@Lax455465.RationalEncoding.RationalInstance.weight n I v).num M) →
                      (∀ (v : Fin n),
                          @LE.le Nat instLENat (@Lax455465.RationalEncoding.RationalInstance.weight n I v).den M) →
                        (∀ (u v : Fin n),
                            @LE.le Nat instLENat (@Lax455465.RationalEncoding.RationalInstance.capacity n I u v).num
                              M) →
                          (∀ (u v : Fin n),
                              @LE.le Nat instLENat (@Lax455465.RationalEncoding.RationalInstance.capacity n I u v).den
                                M) →
                            (∀ (u v : Fin n),
                                Lax455465Proofs.LpInputSize.Height M (@NNRat.cast Rat Rat.instNNRatCast (length u v))) →
                              Lax455465Proofs.LpInputSize.Height M (@NNRat.cast Rat Rat.instNNRatCast delta) →
                                Lax455465Proofs.LpInputSize.Height M
                                    (@NNRat.cast Rat Rat.instNNRatCast
                                      (@HDiv.hDiv NNRat NNRat NNRat (@instHDiv NNRat NNRat.instDiv) delta
                                        (@Nat.cast NNRat
                                          (@AddMonoidWithOne.toNatCast NNRat
                                            (@AddCommMonoidWithOne.toAddMonoidWithOne NNRat
                                              (@NonAssocSemiring.toAddCommMonoidWithOne NNRat
                                                (@Semiring.toNonAssocSemiring NNRat
                                                  (@DivisionSemiring.toSemiring NNRat
                                                    (@Semifield.toDivisionSemiring NNRat NNRat.instSemifield))))))
                                          (Lax455465Proofs.RegionBudget.steps p)))) →
                                  (∀ (active : Finset (Fin n)) (root : Fin n) (i : Nat)
                                      (hi :
                                        @LT.lt Nat instLTNat i
                                          (@List.length NNRat
                                            (@Lax455465Proofs.RadiusData.candidates n (length root)
                                              (fun (v : Fin n) => length v root) (Lax455465Proofs.RegionBudget.steps p)
                                              delta))),
                                      @Lax455465Proofs.RegionQueryHeight.Bounds n
                                        (@Lax455465Proofs.RadiusSearchData.atRadius n
                                          (@Lax455465Proofs.RegionExecutionData.query n I length active root seed beta)
                                          (@GetElem.getElem (List NNRat) Nat NNRat
                                            (fun (as : List NNRat) (i : Nat) =>
                                              @LT.lt Nat instLTNat i (@List.length NNRat as))
                                            (@List.instGetElemNatLtLength NNRat)
                                            (@Lax455465Proofs.RadiusData.candidates n (length root)
                                              (fun (v : Fin n) => length v root) (Lax455465Proofs.RegionBudget.steps p)
                                              delta)
                                            i hi))
                                        H) →
                                    @Eq Rat (@NNRat.cast Rat Rat.instNNRatCast beta)
                                        (Lax455465Proofs.RegionSearch.slope (Lax455465Proofs.RegionBudget.steps p)
                                          (@NNRat.cast Rat Rat.instNNRatCast delta)) →
                                      @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                          (@NNRat.cast Rat Rat.instNNRatCast seed) →
                                        @LT.lt Rat Rat.instLT
                                            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                            (@NNRat.cast Rat Rat.instNNRatCast delta) →
                                          @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))
                                              p →
                                            (∀ (v : Fin n),
                                                @Eq NNRat (length v v)
                                                  (@OfNat.ofNat NNRat (nat_lit 0)
                                                    (@Zero.toOfNat0 NNRat
                                                      (@MulZeroClass.toZero NNRat
                                                        (@instMulZeroClassOfSemiring NNRat
                                                          (@DivisionSemiring.toSemiring NNRat
                                                            (@Semifield.toDivisionSemiring NNRat
                                                              NNRat.instSemifield))))))) →
                                              (∀ (u v w : Fin n),
                                                  @LE.le Rat Rat.instLE (@NNRat.cast Rat Rat.instNNRatCast (length u w))
                                                    (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd)
                                                      (@NNRat.cast Rat Rat.instNNRatCast (length u v))
                                                      (@NNRat.cast Rat Rat.instNNRatCast (length v w)))) →
                                                @LE.le Rat Rat.instLE
                                                    (@Lax455465Proofs.RegionRounding.metricCost n I
                                                      (@Lax455465Proofs.MetricMatrix.rational n length))
                                                    (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                                      (@Nat.cast Rat Rat.instNatCast p)
                                                      (@NNRat.cast Rat Rat.instNNRatCast seed)) →
                                                  @LE.le Nat instLENat
                                                      (@Finset.card (Fin n)
                                                        (@Lax455465Proofs.RegionSelection.support n
                                                          (@Lax455465Proofs.RegionLoop.weights n I
                                                            (@Finset.univ (Fin n) (Fin.fintype n)))))
                                                      p →
                                                    Lax808846Proofs.Reasoning.Spec B
                                                      (fun (σ : Lax808846Proofs.Imp.Env) =>
                                                        And
                                                          (@Lax455465Proofs.RamRegionInvariant.Fixed n I length seed
                                                            beta delta threshold p σ)
                                                          (And (Lax455465Proofs.RamRegionInvariant.Room n p σ)
                                                            (And
                                                              (@Eq Nat (σ.vars "loop.limit")
                                                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) p
                                                                  (@OfNat.ofNat Nat (nat_lit 1)
                                                                    (instOfNatNat (nat_lit 1)))))
                                                              (@Lax455465Proofs.RamRegionState.View n I length seed beta
                                                                (Lax455465Proofs.RamRegionBoundedLoop.initial n) σ))))
                                                      Lax455465Proofs.RamRegionScan.command
                                                      (fun (x τ : Lax808846Proofs.Imp.Env) =>
                                                        And
                                                          (@Lax455465Proofs.RamRegionInvariant.Fixed n I length seed
                                                            beta delta threshold p τ)
                                                          (And (Lax455465Proofs.RamRegionInvariant.Room n p τ)
                                                            (@Lax455465Proofs.RamRegionState.View n I length seed beta
                                                              (@Nat.iterate (Lax455465Proofs.RegionRuntimeState.State n)
                                                                (@Lax455465Proofs.RegionRuntimeState.advance n I length
                                                                  seed beta delta threshold p)
                                                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) p
                                                                  (@OfNat.ofNat Nat (nat_lit 1)
                                                                    (instOfNatNat (nat_lit 1))))
                                                                (Lax455465Proofs.RamRegionBoundedLoop.initial n))
                                                              τ)))
                                                      (Lax455465Proofs.RamRegionBoundedLoop.cost n p M H) := by sorry
