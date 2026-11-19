-- Prove2me | Theorems.Thm_Lax109476Proofs_RamRecoverySelector_selectEntry_spec_native
-- name    : Lax109476Proofs.RamRecoverySelector.selectEntry_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:38:10.200201+00:00
-- url     : https://prove2.me/theorems/6b4571df-c52e-4afc-8b70-12add3be345d
-- title:
--   Selecting an entry of a recovery query matrix
-- statement:
--   Let $P$ have $m$ rational constraints in $n$ variables and let $k<n$. Under the explicit coefficient-height and word-range hypotheses, the fixed recovery-matrix selector reads row $i$ and column $j$ and returns the corresponding entry of the coordinate-cut matrix:
--   $$a=E(P,k)_{ij}.$$
--   The initial state stores the matrix and its dimensions and indices; the operational cost is at most seventy-six steps.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamRecoverySelector.lean#L38

import Definitions.Def_EdgeSublinearMWIS_Main_NativeNextInterfaces
namespace Lax109476Proofs.RamRecoverySelector
end Lax109476Proofs.RamRecoverySelector

theorem Lax109476Proofs.RamRecoverySelector.selectEntry_spec_native : ∀ (B M m n k : Nat) (P : Lax109476.LinearProgram.Program Rat m n),
  @LT.lt Nat instLTNat k n →
    ∀
      (i :
        Fin
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n n))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (j : Fin n),
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
              Lax808846Proofs.Reasoning.Spec B
                (fun (σ : Lax808846Proofs.Imp.Env) =>
                  And
                    (Lax109476Proofs.RamRationalArrays.Represents "point.A"
                      (@Lax109476Proofs.RamMatrixStorage.flatten m n (@Lax109476.LinearProgram.Program.A Rat m n P)) σ)
                    (And (@Eq Nat (σ.vars "point.m") m)
                      (And (@Eq Nat (σ.vars "point.n") n)
                        (And (@Eq Nat (σ.vars "point.k") k)
                          (And
                            (@Eq Nat (σ.vars "query.row")
                              (@Fin.val
                                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n n))
                                  (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                i))
                            (@Eq Nat (σ.vars "query.col") (@Fin.val n j)))))))
                Lax109476Proofs.RamRecoverySelector.selectEntry
                (fun (x τ : Lax808846Proofs.Imp.Env) =>
                  Lax109476Proofs.RamRational.FractionOutput (@Lax109476Proofs.RecoveryQueryEntries.entry m n P k i j)
                    τ)
                (@OfNat.ofNat Nat (nat_lit 76) (instOfNatNat (nat_lit 76))) := by sorry
