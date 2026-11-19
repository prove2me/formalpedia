-- Prove2me | Theorems.Thm_Lax109476Proofs_RamRecoveryQuery_buildQuery_spec_native
-- name    : Lax109476Proofs.RamRecoveryQuery.buildQuery_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:38:19.580059+00:00
-- url     : https://prove2.me/theorems/7a2fc290-5058-4ae9-9f95-0ddc31791292
-- title:
--   Constructing the coordinate-recovery feasibility query
-- statement:
--   Let $P$ be a rational linear program with zero objective, $x$ a rational prefix vector, $k<n$ and $t$ a rational threshold. Suppose their entries have height at most $M\ge1$, the workspace has the stated array extents and all explicit address and word bounds hold. The fixed constructor preserves the recovery data and writes the exact encoded program
--   $$\{y\in P:y_j=x_j\ (j<k),\ y_k\le t\}.$$
--   It terminates within the specified quadratic matrix-size instruction bound.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamRecoveryQuery.lean#L71

import Definitions.Def_EdgeSublinearMWIS_Main_NativeNextInterfaces
namespace Lax109476Proofs.RamRecoveryQuery
end Lax109476Proofs.RamRecoveryQuery

theorem Lax109476Proofs.RamRecoveryQuery.buildQuery_spec_native : ∀ (B M m n k : Nat) (P : Lax109476.LinearProgram.Program Rat m n) (x : Fin n → Rat) (t : Rat)
  (hk : @LT.lt Nat instLTNat k n),
  @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M →
    @LT.lt Nat instLTNat M B →
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
          B →
        (∀ (i : Fin m) (j : Fin n),
            Lax109476Proofs.RationalArithmeticBounds.Height (@Lax109476.LinearProgram.Program.A Rat m n P i j) M) →
          (∀ (i : Fin m),
              Lax109476Proofs.RationalArithmeticBounds.Height (@Lax109476.LinearProgram.Program.b Rat m n P i) M) →
            (∀ (j : Fin n), Lax109476Proofs.RationalArithmeticBounds.Height (x j) M) →
              Lax109476Proofs.RationalArithmeticBounds.Height t M →
                (∀ (j : Fin n),
                    @Eq Rat (@Lax109476.LinearProgram.Program.c Rat m n P j)
                      (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))) →
                  Lax808846Proofs.Reasoning.Spec B
                    (fun (σ : Lax808846Proofs.Imp.Env) =>
                      And (@Lax109476Proofs.RamRecoveryData.Data m n P x k t σ)
                        (Lax109476Proofs.RamRecoveryQuery.Extent m n σ))
                    Lax109476Proofs.RamRecoveryQuery.buildQuery
                    (fun (x_1 τ : Lax808846Proofs.Imp.Env) =>
                      And (@Lax109476Proofs.RamRecoveryData.Data m n P x k t τ)
                        (@Lax109476Proofs.RamStoredProgram.RepresentsProgram
                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n n))
                            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                          n
                          (@Lax109476Proofs.CoordinateOptimization.coordinateCut
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n n))
                            n (@Lax109476Proofs.LexicographicMinima.fixedPrefix m n P x k) (@Fin.mk n k hk) t)
                          τ))
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 142) (instOfNatNat (nat_lit 142)))
                            (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n n))
                                (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                              n))
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                            (@OfNat.ofNat Nat (nat_lit 138) (instOfNatNat (nat_lit 138)))
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n n))
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))))
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 33) (instOfNatNat (nat_lit 33))) n))
                      (@OfNat.ofNat Nat (nat_lit 106) (instOfNatNat (nat_lit 106)))) := by sorry
