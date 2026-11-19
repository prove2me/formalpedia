-- Prove2me | Theorems.Thm_Lax109476Proofs_RamRounding_roundFraction_spec_native
-- name    : Lax109476Proofs.RamRounding.roundFraction_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:21.06308+00:00
-- url     : https://prove2.me/theorems/54403bf5-35d8-4ac4-92ed-8e5de9650418
-- title:
--   Bounded execution of rational downward grid rounding
-- statement:
--   Let $x=(-1)^s n/d$, with $s\le1$, $n,d,D\le M$ and $d,D>0$. Under $2M^2+3<B$, the operand and grid registers specify a fixed command returning downward rounding to the $1/D$ grid. Its cost is at most $36\operatorname{size}(D)+96$:
--
--   $$x_{\rm out}=\lfloor Dx\rfloor/D.$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamRounding.lean, theorem roundFraction_spec (lines 62–91)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax109476Proofs.RamRounding
end Lax109476Proofs.RamRounding

theorem Lax109476Proofs.RamRounding.roundFraction_spec_native : ∀ (B M s n d D : Nat),
  @LT.lt Nat instLTNat
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      B →
    @LE.le Nat instLENat s (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @LE.le Nat instLENat n M →
        @LE.le Nat instLENat d M →
          @LE.le Nat instLENat D M →
            @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d →
              @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) D →
                Lax808846Proofs.Reasoning.Spec B
                  (fun (σ : Lax808846Proofs.Imp.Env) =>
                    And (@Eq Nat (σ.vars "left.s") s)
                      (And (@Eq Nat (σ.vars "left.n") n)
                        (And (@Eq Nat (σ.vars "left.d") d) (@Eq Nat (σ.vars "grid.D") D))))
                  Lax109476Proofs.RamRounding.roundFraction
                  (fun (x σ' : Lax808846Proofs.Imp.Env) =>
                    Lax109476Proofs.RamRational.FractionOutput
                      (Lax109476Proofs.RationalRounding.roundDown (Lax109476Proofs.RamRational.fractionValue s n d) D)
                      σ')
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 36) (instOfNatNat (nat_lit 36))) D.size)
                    (@OfNat.ofNat Nat (nat_lit 96) (instOfNatNat (nat_lit 96)))) := by sorry
