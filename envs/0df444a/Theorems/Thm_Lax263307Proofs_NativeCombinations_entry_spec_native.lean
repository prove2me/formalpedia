-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeCombinations_entry_spec_native
-- name    : Lax263307Proofs.NativeCombinations.entry_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:38:15.527034+00:00
-- url     : https://prove2.me/theorems/499f67d3-e379-4123-90bc-89d763c8d80a
-- title:
--   Computing one binomial-table entry
-- statement:
--   Let $i\le n$ and $j\le k$. Suppose the binomial table prefix before coordinate $(i,j)$ is stored, every required coefficient is below $B$, and the complete table addresses fit the stated word bound. Then the fixed entry command returns
--   $$v=\binom{i}{j}$$
--   in at most thirty bounded operational steps. This is the local contract for building the subset-enumeration table.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeCombinations.lean#L100

import Definitions.Def_EdgeSublinearMWIS_Main_NativeNextInterfaces
namespace Lax263307Proofs.NativeCombinations
end Lax263307Proofs.NativeCombinations

theorem Lax263307Proofs.NativeCombinations.entry_spec_native : ∀ (B n k i j : Nat),
  @LE.le Nat instLENat i n →
    @LE.le Nat instLENat j k →
      @LT.lt Nat instLTNat
          (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) n
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                    (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                n)
              k)
            (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
          B →
        (∀ (i : Nat),
            @LE.le Nat instLENat i n → ∀ (j : Nat), @LE.le Nat instLENat j k → @LT.lt Nat instLTNat (i.choose j) B) →
          Lax808846Proofs.Reasoning.Spec B
            (fun (σ : Lax808846Proofs.Imp.Env) =>
              And (@Eq Nat (σ.vars "choose.row") i)
                (And (@Eq Nat (σ.vars "choose.col") j)
                  (And
                    (@Eq Nat (σ.vars "choose.cols")
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (Lax455465Proofs.RamVirtualState.Prefix
                      (@List.take Nat
                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) i
                            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                          j)
                        (Lax263307Proofs.NativeCombinations.table n k))
                      "choose.table" σ))))
            Lax263307Proofs.NativeCombinations.entry
            (fun (x τ : Lax808846Proofs.Imp.Env) => @Eq Nat (τ.vars "choose.value") (i.choose j))
            (@OfNat.ofNat Nat (nat_lit 30) (instOfNatNat (nat_lit 30))) := by sorry
