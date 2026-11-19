-- Prove2me | Theorems.Thm_Lax109476Proofs_RamRounding_upperRootFraction_spec_native
-- name    : Lax109476Proofs.RamRounding.upperRootFraction_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:35.240979+00:00
-- url     : https://prove2.me/theorems/52f79f50-9bb0-47b0-ad10-af0337657979
-- title:
--   Bounded execution of the rational upper-root routine
-- statement:
--   Let $x=(-1)^s n/d$, where $s\le1$, $n,d,D\le M$ and $d,D>0$. Under $(2(M^3+2)+1)^2+M^3+3<B$ and initialized operand/grid registers, the fixed upper-root command returns $u_D(x)$ as a reduced fraction. Here
--
--   $$u_D(x)=\frac{\lfloor\sqrt{\max\{0,\lceil xD^2\rceil\}}\rfloor+1}{D}.$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamRounding.lean, theorem upperRootFraction_spec (lines 134–183)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax109476Proofs.RamRounding
end Lax109476Proofs.RamRounding

theorem Lax109476Proofs.RamRounding.upperRootFraction_spec_native : ∀ (B M s n d D : Nat),
  @LT.lt Nat instLTNat
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
              (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
                    (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
            (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
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
                  Lax109476Proofs.RamRounding.upperRootFraction
                  (fun (x σ' : Lax808846Proofs.Imp.Env) =>
                    Lax109476Proofs.RamRational.FractionOutput
                      (Lax109476Proofs.RationalRounding.sqrtUpper (Lax109476Proofs.RamRational.fractionValue s n d) D)
                      σ')
                  (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                    (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 26) (instOfNatNat (nat_lit 26)))
                        (Lax109476Proofs.RamRounding.upperMagnitude s n d D).size)
                      (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                        (@OfNat.ofNat Nat (nat_lit 36) (instOfNatNat (nat_lit 36))) D.size))
                    (@OfNat.ofNat Nat (nat_lit 128) (instOfNatNat (nat_lit 128)))) := by sorry
