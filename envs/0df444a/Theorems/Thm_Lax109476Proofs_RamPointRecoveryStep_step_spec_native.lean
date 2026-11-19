-- Prove2me | Theorems.Thm_Lax109476Proofs_RamPointRecoveryStep_step_spec_native
-- name    : Lax109476Proofs.RamPointRecoveryStep.step_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:26:07.92792+00:00
-- url     : https://prove2.me/theorems/3baf1b3b-1bc8-4706-9d8c-19f854f5e586
-- title:
--   One bounded coordinate-recovery step
-- statement:
--   Let $P$ and $x$ satisfy rational feasibility and coordinatewise lexicographic minimality, with zero objective. Suppose $k<n$, all coefficients and solution coordinates meet the stated height bounds, and the complete midpoint, query-size, reconstruction, denominator and host-width guards hold. If the persistent storage contains exactly the first $k$ coordinates of $x$, one fixed step extends it to
--   $$\operatorname{prefix}(x,k+1),\qquad k_{\rm out}=k+1.$$
--   The bound register and reconstruction-stack length are preserved, with the source's explicit coordinate-step instruction bound. This is the invariant-preserving step of full point recovery.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamPointRecoveryStep.lean, theorem Lax109476Proofs.RamPointRecoveryStep.step_spec, line 34

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
namespace Lax109476Proofs.RamPointRecoveryStep
end Lax109476Proofs.RamPointRecoveryStep

theorem Lax109476Proofs.RamPointRecoveryStep.step_spec_native : ∀ (S N w D M m n k : Nat) (P : Lax109476.LinearProgram.Program Rat m n) (x : Fin n → Rat),
  @LT.lt Nat instLTNat k n →
    @LT.lt Nat instLTNat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
          (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w) →
      @LT.lt Nat instLTNat (Lax109476Proofs.BinaryOptimization.steps D)
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w) →
        @LE.le Nat instLENat
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) D
                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Lax109476Proofs.BinaryOptimization.steps D)))
            M →
          @LE.le Nat instLENat M
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) S) →
            @LE.le Nat instLENat
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (Lax109476Proofs.RamRationalReconstruction.depthBound S)
                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                N →
              @LE.le Nat instLENat (Lax109476Proofs.RamRationalReconstruction.wordWidth S) w →
                @LT.lt Nat instLTNat D
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w) →
                  @LT.lt Nat instLTNat
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n n))
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              n)
                            m)
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n n))
                        (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w) →
                    @LE.le Nat instLENat
                        (Lax109476Proofs.RamStoredFeasibility.wordWidth
                          (Lax109476Proofs.RamRecoveryThreshold.sizeBound m n
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                              (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                              (@HPow.hPow Nat Nat Nat
                                (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                        w →
                      (∀ (i : Fin m) (j : Fin n),
                          Lax109476Proofs.RationalArithmeticBounds.Height
                            (@Lax109476.LinearProgram.Program.A Rat m n P i j) M) →
                        (∀ (i : Fin m),
                            Lax109476Proofs.RationalArithmeticBounds.Height
                              (@Lax109476.LinearProgram.Program.b Rat m n P i) M) →
                          (∀ (j : Fin n), Lax109476Proofs.RationalArithmeticBounds.Height (x j) M) →
                            (∀ (j : Fin n),
                                @Eq Rat (@Lax109476.LinearProgram.Program.c Rat m n P j)
                                  (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) →
                              @Lax109476.LinearProgram.PrimalFeasible Real Real.instRing Real.partialOrder m n
                                  (@Lax109476.RationalCertificates.toReal m n P)
                                  (@Lax109476.RationalCertificates.realVector n x) →
                                (∀ (i : Fin n) (y : Fin n → Real),
                                    @Lax109476.LinearProgram.PrimalFeasible Real Real.instRing Real.partialOrder m n
                                        (@Lax109476.RationalCertificates.toReal m n P) y →
                                      (∀ (j : Fin n),
                                          @LT.lt (Fin n) (@instLTFin n) j i →
                                            @Eq Real (y j) (@Rat.cast Real Real.instRatCast (x j))) →
                                        @LE.le Real Real.instLE (@Rat.cast Real Real.instRatCast (x i)) (y i)) →
                                  (∀ (j : Fin n),
                                      And (@LE.le Rat Rat.instLE (x j) (@Nat.cast Rat Rat.instNatCast D))
                                        (@LE.le Nat instLENat (x j).den D)) →
                                    Lax808846Proofs.Reasoning.Spec
                                      (@HPow.hPow Nat Nat Nat
                                        (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                                      (fun (σ : Lax808846Proofs.Imp.Env) =>
                                        And
                                          (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P
                                            (@Lax109476Proofs.PointRecovery.prefixVector n x k) k σ)
                                          (And (@Eq Nat (σ.vars "minimum.bound") D)
                                            (@Eq Nat (@List.length Nat (σ.arrs "cf.stack")) N)))
                                      Lax109476Proofs.RamPointRecoveryStep.step
                                      (fun (σ τ : Lax808846Proofs.Imp.Env) =>
                                        And
                                          (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P
                                            (@Lax109476Proofs.PointRecovery.prefixVector n x
                                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                            τ)
                                          (And (@Eq Nat (τ.vars "minimum.bound") D)
                                            (And (@Eq Nat (@List.length Nat (τ.arrs "cf.stack")) N)
                                              (@Eq Nat (τ.vars "point.k")
                                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (σ.vars "point.k")
                                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))))
                                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                        (Lax109476Proofs.RamPointRecoveryStep.coordinateCost S D M m n)
                                        (@OfNat.ofNat Nat (nat_lit 25) (instOfNatNat (nat_lit 25)))) := by sorry
