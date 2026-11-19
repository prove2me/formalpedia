-- Prove2me | Theorems.Thm_Lax109476Proofs_RamRecoveryThreshold_decideThreshold_spec_native
-- name    : Lax109476Proofs.RamRecoveryThreshold.decideThreshold_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:33:35.184681+00:00
-- url     : https://prove2.me/theorems/52de6698-be7c-4a76-80df-84a0d9c89d40
-- title:
--   Operational threshold query for coordinate recovery
-- statement:
--   Let $P$ be a rational linear program with zero objective, let $x$ be a rational prefix candidate and let $k<n$. Suppose all coefficients, prefix entries and a rational threshold $t$ have height at most $M\ge1$. Under the explicit word-width and workspace bounds, the fixed threshold command preserves the stored recovery data and returns exactly the feasibility truth value of
--   $$\{y\in P:y_j=x_j\ (j<k),\ y_k\le t\}.$$
--   Its bounded operational execution uses at most the specified instruction bound. No feasibility promise is imposed on the query.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamRecoveryThreshold.lean#L74

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
namespace Lax109476Proofs.RamRecoveryThreshold
end Lax109476Proofs.RamRecoveryThreshold

theorem Lax109476Proofs.RamRecoveryThreshold.decideThreshold_spec_native : ∀ (m n k M w : Nat) (P : Lax109476.LinearProgram.Program Rat m n) (x : Fin n → Rat) (t : Rat)
  (hk : @LT.lt Nat instLTNat k n),
  @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M →
    @LT.lt Nat instLTNat M
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
            (Lax109476Proofs.RamStoredFeasibility.wordWidth (Lax109476Proofs.RamRecoveryThreshold.sizeBound m n M)) w →
          (∀ (i : Fin m) (j : Fin n),
              Lax109476Proofs.RationalArithmeticBounds.Height (@Lax109476.LinearProgram.Program.A Rat m n P i j) M) →
            (∀ (i : Fin m),
                Lax109476Proofs.RationalArithmeticBounds.Height (@Lax109476.LinearProgram.Program.b Rat m n P i) M) →
              (∀ (j : Fin n), Lax109476Proofs.RationalArithmeticBounds.Height (x j) M) →
                Lax109476Proofs.RationalArithmeticBounds.Height t M →
                  (∀ (j : Fin n),
                      @Eq Rat (@Lax109476.LinearProgram.Program.c Rat m n P j)
                        (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) →
                    Lax808846Proofs.Reasoning.Spec
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                      (fun (σ : Lax808846Proofs.Imp.Env) =>
                        And (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P x k σ)
                          (Lax109476Proofs.RamRationalScalars.Value "bisect.mid" t σ))
                      Lax109476Proofs.RamRecoveryThreshold.decideThreshold
                      (fun (x_1 τ : Lax808846Proofs.Imp.Env) =>
                        And (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P x k τ)
                          (@Eq (Option Bool)
                            (Lax808846Proofs.Imp.Cond.evalB
                              (@HPow.hPow Nat Nat Nat
                                (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) w)
                              Lax109476Proofs.RamBisectionCommit.condition τ)
                            (@Option.some Bool
                              (@Lax109476Proofs.RationalFeasibilityDecision.feasible
                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n n))
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                n
                                (@Lax109476Proofs.CoordinateOptimization.coordinateCut
                                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n n))
                                  n (@Lax109476Proofs.LexicographicMinima.fixedPrefix m n P x k) (@Fin.mk n k hk) t)))))
                      (Lax109476Proofs.RamRecoveryThreshold.instructionBound m n M) := by sorry
