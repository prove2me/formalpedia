-- Prove2me | Theorems.Thm_Lax109476Proofs_RamPointRecoveryBounds_recover_bounded_spec_native
-- name    : Lax109476Proofs.RamPointRecoveryBounds.recover_bounded_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:26:07.417187+00:00
-- url     : https://prove2.me/theorems/f6d9b87f-ad86-4fcb-8cac-a4e00791d2a4
-- title:
--   Uniform bounded execution of lexicographic point recovery
-- statement:
--   Let $P$ be a rational system with $m$ rows, $n$ variables and zero objective. Let $x$ be a rational feasible point that is minimal in each coordinate among feasible real points agreeing with all its earlier coordinates. Assume the published coefficient, solution-height, coordinate/denominator, reconstruction-depth and word-width bounds with parameters $S,C,N,D,w$. Starting from its persistent zero-length prefix, the fixed recovery loop stores the entire vector exactly:
--   $$x_{\rm final}=x,\qquad k_{\rm final}=n.$$
--   It retains the bound $D$ and continued-fraction stack length $N$, within the source's explicit instruction bound $T(m,n,S,C)$.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamPointRecoveryBounds.lean, theorem Lax109476Proofs.RamPointRecoveryBounds.recover_bounded_spec, line 59

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces
namespace Lax109476Proofs.RamPointRecoveryBounds
end Lax109476Proofs.RamPointRecoveryBounds

theorem Lax109476Proofs.RamPointRecoveryBounds.recover_bounded_spec_native : ∀ (m n S C N D w : Nat) (P : Lax109476.LinearProgram.Program Rat m n) (x : Fin n → Rat),
  @LE.le Nat instLENat D.size C →
    @LE.le Nat instLENat
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
            C)
          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        S →
      @LE.le Nat instLENat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (Lax109476Proofs.RamRationalReconstruction.depthBound S)
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          N →
        @LE.le Nat instLENat (Lax109476Proofs.RamPointRecoveryBounds.wordWidth m n S) w →
          (∀ (i : Fin m) (j : Fin n),
              Lax109476Proofs.RationalArithmeticBounds.Height (@Lax109476.LinearProgram.Program.A Rat m n P i j)
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) S)) →
            (∀ (i : Fin m),
                Lax109476Proofs.RationalArithmeticBounds.Height (@Lax109476.LinearProgram.Program.b Rat m n P i)
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) S)) →
              (∀ (j : Fin n),
                  Lax109476Proofs.RationalArithmeticBounds.Height (x j)
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) S)) →
                (∀ (j : Fin n),
                    @Eq Rat (@Lax109476.LinearProgram.Program.c Rat m n P j)
                      (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) →
                  @Lax109476.LinearProgram.PrimalFeasible Real Real.instRing Real.partialOrder m n
                      (@Lax109476.RationalCertificates.toReal m n P) (@Lax109476.RationalCertificates.realVector n x) →
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
                                (@Lax109476Proofs.PointRecovery.prefixVector n x
                                  (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                                (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) σ)
                              (And (@Eq Nat (σ.vars "minimum.bound") D)
                                (@Eq Nat (@List.length Nat (σ.arrs "cf.stack")) N)))
                          Lax109476Proofs.RamPointRecovery.recover
                          (fun (x_1 τ : Lax808846Proofs.Imp.Env) =>
                            And (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P x n τ)
                              (And (@Eq Nat (τ.vars "minimum.bound") D)
                                (@Eq Nat (@List.length Nat (τ.arrs "cf.stack")) N)))
                          (Lax109476Proofs.RamPointRecoveryBounds.instructionBound m n S C) := by sorry
