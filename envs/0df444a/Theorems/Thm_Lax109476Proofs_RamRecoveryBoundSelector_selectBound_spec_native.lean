-- Prove2me | Theorems.Thm_Lax109476Proofs_RamRecoveryBoundSelector_selectBound_spec_native
-- name    : Lax109476Proofs.RamRecoveryBoundSelector.selectBound_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:38:14.96425+00:00
-- url     : https://prove2.me/theorems/9d6541ca-238b-4d47-a07f-69b87b279c5c
-- title:
--   Selecting a recovery query right-hand-side entry
-- statement:
--   Let $P$ be a rational linear program, $x$ a rational prefix vector, $k<n$ and $t$ a rational threshold. Under the stated height and word-range bounds, the fixed right-hand-side selector returns
--   $$b=B(P,x,k,t)_i$$
--   for each query row $i$, from the stored constraint bounds, prefix values and threshold. It uses at most eighty bounded operational steps.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamRecoveryBoundSelector.lean#L27

import Definitions.Def_EdgeSublinearMWIS_Main_NativeNextInterfaces
namespace Lax109476Proofs.RamRecoveryBoundSelector
end Lax109476Proofs.RamRecoveryBoundSelector

theorem Lax109476Proofs.RamRecoveryBoundSelector.selectBound_spec_native : ∀ (B M m n k : Nat) (P : Lax109476.LinearProgram.Program Rat m n) (x : Fin n → Rat),
  @LT.lt Nat instLTNat k n →
    ∀ (t : Rat)
      (i :
        Fin
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n n))
            (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))),
      @LE.le Nat instLENat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) M →
        @LT.lt Nat instLTNat M B →
          @LT.lt Nat instLTNat
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n n))
                (@OfNat.ofNat Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
              B →
            (∀ (i : Fin m),
                Lax109476Proofs.RationalArithmeticBounds.Height (@Lax109476.LinearProgram.Program.b Rat m n P i) M) →
              (∀ (j : Fin n), Lax109476Proofs.RationalArithmeticBounds.Height (x j) M) →
                Lax109476Proofs.RationalArithmeticBounds.Height t M →
                  Lax808846Proofs.Reasoning.Spec B
                    (fun (σ : Lax808846Proofs.Imp.Env) =>
                      And
                        (Lax109476Proofs.RamRationalArrays.Represents "point.b"
                          (@List.ofFn Rat m (@Lax109476.LinearProgram.Program.b Rat m n P)) σ)
                        (And (Lax109476Proofs.RamRationalArrays.Represents "point.x" (@List.ofFn Rat n x) σ)
                          (And (Lax109476Proofs.RamRationalScalars.Value "bisect.mid" t σ)
                            (And (@Eq Nat (σ.vars "point.m") m)
                              (And (@Eq Nat (σ.vars "point.n") n)
                                (And (@Eq Nat (σ.vars "point.k") k)
                                  (@Eq Nat (σ.vars "query.row")
                                    (@Fin.val
                                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) m
                                          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n n))
                                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                                      i))))))))
                    Lax109476Proofs.RamRecoveryBoundSelector.selectBound
                    (fun (x_1 τ : Lax808846Proofs.Imp.Env) =>
                      Lax109476Proofs.RamRational.FractionOutput
                        (@Lax109476Proofs.RecoveryQueryEntries.bound m n P x k t i) τ)
                    (@OfNat.ofNat Nat (nat_lit 80) (instOfNatNat (nat_lit 80))) := by sorry
