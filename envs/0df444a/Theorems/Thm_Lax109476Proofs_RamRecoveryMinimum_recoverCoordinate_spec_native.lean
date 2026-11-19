-- Prove2me | Theorems.Thm_Lax109476Proofs_RamRecoveryMinimum_recoverCoordinate_spec_native
-- name    : Lax109476Proofs.RamRecoveryMinimum.recoverCoordinate_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:02:17.581695+00:00
-- url     : https://prove2.me/theorems/87ae5350-a24e-4f01-9a15-25160f182a6a
-- title:
--   Execute one functional coordinate-minimum recovery query
-- statement:
--   Let $P$ be a rational zero-objective system, let $x$ be a stored prefix vector, and let $k<n$. Suppose coefficients and stored coordinates have height at most $M$, and the complete binary-optimization, reconstruction, denominator, query-size and host-width guards hold. From persistent storage and a bound $D$, the fixed command returns exactly the functional coordinate-minimum procedure for the prefix-fixed system:
--   $$\operatorname{out}=\operatorname{coordinateMinimum}(P[x_{<k}],k,D).$$
--   It preserves the persistent input and satisfies the explicit instruction bound. No feasibility or lexicographic-minimality premise is needed for this operational equality; those facts are used separately to identify the returned value.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamRecoveryMinimum.lean, theorem Lax109476Proofs.RamRecoveryMinimum.recoverCoordinate_spec, line 52

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
namespace Lax109476Proofs.RamRecoveryMinimum
end Lax109476Proofs.RamRecoveryMinimum

theorem Lax109476Proofs.RamRecoveryMinimum.recoverCoordinate_spec_native : ∀ (S N w D M m n k : Nat) (P : Lax109476.LinearProgram.Program Rat m n) (x : Fin n → Rat)
  (hk : @LT.lt Nat instLTNat k n),
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
                            Lax808846Proofs.Reasoning.Spec
                              (@HPow.hPow Nat Nat Nat
                                (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                              (fun (σ : Lax808846Proofs.Imp.Env) =>
                                And (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P x k σ)
                                  (And (@Eq Nat (σ.vars "minimum.bound") D)
                                    (@Eq Nat (@List.length Nat (σ.arrs "cf.stack")) N)))
                              Lax109476Proofs.RamRecoveryMinimum.recoverCoordinate
                              (fun (x_1 τ : Lax808846Proofs.Imp.Env) =>
                                And (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P x k τ)
                                  (Lax109476Proofs.RamReconstructionRecord.Output
                                    (@Lax109476Proofs.CoordinateOptimization.coordinateMinimum
                                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n n))
                                      n (@Lax109476Proofs.LexicographicMinima.fixedPrefix m n P x k) (@Fin.mk n k hk) D)
                                    τ))
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                            (@OfNat.ofNat Nat (nat_lit 144) (instOfNatNat (nat_lit 144))) M.size)
                                          (@OfNat.ofNat Nat (nat_lit 342) (instOfNatNat (nat_lit 342))))
                                        (Lax109476Proofs.RamRecoveryThreshold.instructionBound m n
                                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                            (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
                                            (@HPow.hPow Nat Nat Nat
                                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                              M (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                                      (Lax109476Proofs.BinaryOptimization.steps D))
                                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                      (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))) D.size))
                                  (Lax109476Proofs.RamRationalReconstruction.instructionBound S))
                                (@OfNat.ofNat Nat (nat_lit 48) (instOfNatNat (nat_lit 48)))) := by sorry
