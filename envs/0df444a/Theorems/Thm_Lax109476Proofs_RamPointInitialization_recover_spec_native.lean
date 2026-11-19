-- Prove2me | Theorems.Thm_Lax109476Proofs_RamPointInitialization_recover_spec_native
-- name    : Lax109476Proofs.RamPointInitialization.recover_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T15:01:14.557851+00:00
-- url     : https://prove2.me/theorems/795b7e32-496d-499c-9631-6f050bd15011
-- title:
--   Initialize and recover the lexicographically least rational feasible point
-- statement:
--   Let $P$ be a rational linear program with $m$ rows and $n$ variables, zero objective, and a rational feasible vector $x$. Assume each coordinate of $x$ is minimal among feasible real vectors agreeing on all earlier coordinates. Suppose coefficient and solution heights are at most $2^S$, each coordinate and denominator is at most $D$, and the published bounds on $D$, reconstruction depth, stack length $N$ and word width $w$ hold. From the stored system, workspace and zero-initializable point buffer, the fixed recovery command stores all coordinates exactly:
--   $$x_{\rm stored}=x.$$
--   It retains the bound $D$ and stack length $N$, with instruction bound $33n+22+T_{\rm recovery}(m,n,S,C)$. This initializes the complete coordinate-recovery execution used by exact certificate construction.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamPointInitialization.lean, theorem Lax109476Proofs.RamPointInitialization.recover_spec, line 47

import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
namespace Lax109476Proofs.RamPointInitialization
end Lax109476Proofs.RamPointInitialization

theorem Lax109476Proofs.RamPointInitialization.recover_spec_native : ∀ (m n S C N D w : Nat) (P : Lax109476.LinearProgram.Program Rat m n) (x : Fin n → Rat),
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
                            And (@Lax109476Proofs.RamPointInitialization.Base m n P σ)
                              (And (Lax109476Proofs.RamRecoveryThreshold.Workspace m n σ)
                                (And (Lax109476Proofs.RamEllipsoidStep.Extents "point.x" n σ)
                                  (And (@Eq Nat (σ.vars "minimum.bound") D)
                                    (@Eq Nat (@List.length Nat (σ.arrs "cf.stack")) N)))))
                          Lax109476Proofs.RamPointInitialization.recover
                          (fun (x_1 τ : Lax808846Proofs.Imp.Env) =>
                            And (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P x n τ)
                              (And (@Eq Nat (τ.vars "minimum.bound") D)
                                (@Eq Nat (@List.length Nat (τ.arrs "cf.stack")) N)))
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                                (@OfNat.ofNat Nat (nat_lit 33) (instOfNatNat (nat_lit 33))) n)
                              (@OfNat.ofNat Nat (nat_lit 22) (instOfNatNat (nat_lit 22))))
                            (Lax109476Proofs.RamPointRecoveryBounds.instructionBound m n S C)) := by sorry
