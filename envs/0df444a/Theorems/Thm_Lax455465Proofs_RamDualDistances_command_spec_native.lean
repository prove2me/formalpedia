-- Prove2me | Theorems.Thm_Lax455465Proofs_RamDualDistances_command_spec_native
-- name    : Lax455465Proofs.RamDualDistances.command_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:02:17.088573+00:00
-- url     : https://prove2.me/theorems/decf5be7-d63d-430b-999f-1f44e346ddbe
-- title:
--   Compute the exact native dual-distance matrix
-- statement:
--   Let $y$ be a nonnegative rational dual vector for an $n$-vertex flow system, with numerator magnitudes and denominators at most $2^w$. Suppose the complete host arithmetic and index guards hold and the two metric buffers have the required lengths. From the stored dual vector, the fixed command computes and stores the exact shortest-distance result:
--   $$d_{\rm out}=\operatorname{dualDistance}(y).$$
--   It also returns metric dimension registers $n,n^2$ and has the explicit cubic-loop instruction bound $50n^2+12+n((72w(n^2+1)+324)n^2+22)+10$.
-- source:
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamDualDistances.lean, theorem Lax455465Proofs.RamDualDistances.command_spec, line 21

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
namespace Lax455465Proofs.RamDualDistances
end Lax455465Proofs.RamDualDistances

theorem Lax455465Proofs.RamDualDistances.command_spec_native : ∀ (B w : Nat) {n : Nat} (y : Fin (Lax455465Proofs.RamFlowData.rows n) → Rat)
  (hy :
    ∀ (i : Fin (Lax455465Proofs.RamFlowData.rows n)),
      @LE.le Rat Rat.instLE (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) (y i)),
  @LT.lt Nat instLTNat
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) w
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      B →
    @LT.lt Nat instLTNat n B →
      @LT.lt Nat instLTNat (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n) B →
        @LT.lt Nat instLTNat
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            B →
          (∀ (i : Fin (Lax455465Proofs.RamFlowData.rows n)),
              @LE.le Nat instLENat (y i).num.natAbs
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)) →
            (∀ (i : Fin (Lax455465Proofs.RamFlowData.rows n)),
                @LE.le Nat instLENat (y i).den
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)) →
              Lax808846Proofs.Reasoning.Spec B
                (fun (σ : Lax808846Proofs.Imp.Env) =>
                  And (@Eq Nat (σ.vars "lp.n") n)
                    (And (@Eq Nat (σ.vars "lp.n2") (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                      (And
                        (Lax455465Proofs.RamVirtualState.Prefix
                          (Lax455465Proofs.RamUnsignedBuffer.encode
                            (@Lax455465Proofs.RamOptimalDecode.vector (Lax455465Proofs.RamFlowData.rows n) y hy))
                          "flow.dual" σ)
                        (And
                          (@LT.lt Nat instLTNat
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                            (@List.length Nat (σ.arrs "metric.old")))
                          (@LT.lt Nat instLTNat
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                              (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                            (@List.length Nat (σ.arrs "metric.new")))))))
                Lax455465Proofs.RamDualDistances.command
                (fun (x τ : Lax808846Proofs.Imp.Env) =>
                  And (@Eq Nat (τ.vars "metric.n") n)
                    (And (@Eq Nat (τ.vars "metric.n2") (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                      (Lax455465Proofs.RamVirtualState.Prefix
                        (Lax455465Proofs.RamUnsignedBuffer.encode
                          (@Lax455465Proofs.MetricMatrix.values n (@Lax455465Proofs.RamDualDistances.result n y hy)))
                        "metric.old" τ)))
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 50) (instOfNatNat (nat_lit 50)))
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                    (@OfNat.ofNat Nat (nat_lit 12) (instOfNatNat (nat_lit 12))))
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                              (@OfNat.ofNat Nat (nat_lit 72) (instOfNatNat (nat_lit 72)))
                              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) w
                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n)
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                            (@OfNat.ofNat Nat (nat_lit 324) (instOfNatNat (nat_lit 324))))
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) n n))
                        (@OfNat.ofNat Nat (nat_lit 22) (instOfNatNat (nat_lit 22)))))
                    (@OfNat.ofNat Nat (nat_lit 10) (instOfNatNat (nat_lit 10))))) := by sorry
