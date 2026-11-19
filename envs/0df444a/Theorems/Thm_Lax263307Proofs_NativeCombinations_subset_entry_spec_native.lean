-- Prove2me | Theorems.Thm_Lax263307Proofs_NativeCombinations_subset_entry_spec_native
-- name    : Lax263307Proofs.NativeCombinations.subset_entry_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T16:38:11.479079+00:00
-- url     : https://prove2.me/theorems/8d50b9e2-8554-446c-b380-3e504676b86f
-- title:
--   One bounded step of ranked subset enumeration
-- statement:
--   Suppose $i<n$, the remaining selection count is at most $k$, the current rank is below $B$, and all required binomial coefficients and table addresses are below $B$. Given the full binomial table prefix, the fixed subset-entry command returns the next inclusion bit and updates the remaining count and rank exactly according to the enumeration transition:
--   $$ (b,u',r')=\operatorname{advance}(n-i,u,r). $$
--   The operational cost is at most forty steps.
-- source:
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeCombinations.lean#L304

import Definitions.Def_EdgeSublinearMWIS_Main_NativeNextInterfaces
namespace Lax263307Proofs.NativeCombinations
end Lax263307Proofs.NativeCombinations

theorem Lax263307Proofs.NativeCombinations.subset_entry_spec_native : ∀ (B n k i need rank : Nat),
  @LT.lt Nat instLTNat i n →
    @LE.le Nat instLENat need k →
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
        @LT.lt Nat instLTNat rank B →
          (∀ (i : Nat),
              @LE.le Nat instLENat i n → ∀ (j : Nat), @LE.le Nat instLENat j k → @LT.lt Nat instLTNat (i.choose j) B) →
            Lax808846Proofs.Reasoning.Spec B
              (fun (σ : Lax808846Proofs.Imp.Env) =>
                And (@Eq Nat (σ.vars "choose.n") n)
                  (And
                    (@Eq Nat (σ.vars "choose.cols")
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                        (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                    (And (@Eq Nat (σ.vars "subset.i") i)
                      (And (@Eq Nat (σ.vars "subset.need") need)
                        (And (@Eq Nat (σ.vars "subset.rank") rank)
                          (Lax455465Proofs.RamVirtualState.Prefix (Lax263307Proofs.NativeCombinations.table n k)
                            "choose.table" σ))))))
              Lax263307Proofs.NativeCombinations.subsetEntry
              (fun (x τ : Lax808846Proofs.Imp.Env) =>
                And
                  (@Eq Nat (τ.vars "subset.bit")
                    (@Prod.fst Nat (Prod Nat Nat)
                      (Lax263307Proofs.NativeCombinations.advance
                        (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) n i) need rank)))
                  (And
                    (@Eq Nat (τ.vars "subset.need")
                      (@Prod.fst Nat Nat
                        (@Prod.snd Nat (Prod Nat Nat)
                          (Lax263307Proofs.NativeCombinations.advance
                            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) n i) need rank))))
                    (@Eq Nat (τ.vars "subset.rank")
                      (@Prod.snd Nat Nat
                        (@Prod.snd Nat (Prod Nat Nat)
                          (Lax263307Proofs.NativeCombinations.advance
                            (@HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) n i) need rank))))))
              (@OfNat.ofNat Nat (nat_lit 40) (instOfNatNat (nat_lit 40))) := by sorry
