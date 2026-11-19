-- Prove2me | Theorems.Thm_Lax109476Proofs_RamSearchLoop_searchLoop_spec_native
-- name    : Lax109476Proofs.RamSearchLoop.searchLoop_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:02:19.510897+00:00
-- url     : https://prove2.me/theorems/0d925483-9f39-4803-a313-8d1da629783c
-- title:
--   Execute the initialized bounded ellipsoid-search loop
-- statement:
--   Let $A$ be an integer $m\times n$ matrix with $n\ge2$ and coefficient magnitudes at most $2^\ell$, and let the rational vector $b$ have the same height bound. Assume $N<2^w$ and the complete ellipsoid bit-width, dimension and separation arithmetic guards. Starting from the source’s full initialized invariant, the native loop runs through its bounded search and returns
--   $$\operatorname{Invariant}_{A,b,N}\ \land\ \neg\operatorname{continue}.$$
--   Its instruction count is at most $(T_{\rm step}(m,n,N,\ell)+4)N+4$. The invariant retains the exact trajectory and first-success interpretation of the output flag and index.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamSearchLoop.lean, theorem Lax109476Proofs.RamSearchLoop.searchLoop_spec, line 64

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
namespace Lax109476Proofs.RamSearchLoop
end Lax109476Proofs.RamSearchLoop

theorem Lax109476Proofs.RamSearchLoop.searchLoop_spec_native : ∀ {m n : Nat} (A : Matrix (Fin m) (Fin n) Int) (b : Fin m → Rat),
  @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n →
    ∀ (N l w : Nat),
      @LT.lt Nat instLTNat N
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w) →
        (∀ (i : Fin m) (j : Fin n),
            @LE.le Nat instLENat (A i j).natAbs
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) l)) →
          (∀ (i : Fin m),
              Lax109476Proofs.RationalArithmeticBounds.Height (b i)
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) l)) →
            @LE.le Nat instLENat
                (Lax109476Proofs.RamEllipsoidBitBounds.wordWidth n (Lax109476Proofs.RamTrajectoryBounds.stateBits n N l)
                  N)
                w →
              @LT.lt Nat instLTNat
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m n)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) m n))
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w) →
                @LT.lt Nat instLTNat
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                        (@HPow.hPow Nat Nat Nat
                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                          (Lax109476Proofs.RamDotProduct.cap n
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (Lax109476Proofs.RamTrajectoryBounds.stateBits n N l)))
                          (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w) →
                  Lax808846Proofs.Reasoning.Spec
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                    (fun (σ : Lax808846Proofs.Imp.Env) =>
                      And
                        (@Lax109476Proofs.RamSearchStep.State m n A b
                          (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) σ)
                        (And (@Eq Nat (σ.vars "search.limit") N)
                          (@Eq Nat (σ.vars "search.found") (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))
                    Lax109476Proofs.RamSearchLoop.searchLoop
                    (fun (x τ : Lax808846Proofs.Imp.Env) =>
                      And (@Lax109476Proofs.RamSearchLoop.Invariant m n A b N τ)
                        (@Eq (Option Bool)
                          (Lax808846Proofs.Imp.Cond.evalB
                            (@HPow.hPow Nat Nat Nat
                              (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                            (Lax808846Proofs.Imp.Cond.lt (Lax808846Proofs.Imp.Expr.var "iter.k")
                              (Lax808846Proofs.Imp.Expr.var "search.limit"))
                            τ)
                          (@Option.some Bool Bool.false)))
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) (Lax109476Proofs.RamSearchStep.cost m n N l)
                          (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
                        N)
                      (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))) := by sorry
