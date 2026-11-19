-- Prove2me | Theorems.Thm_Lax109476Proofs_RamRational_multiplyFraction_spec_native
-- name    : Lax109476Proofs.RamRational.multiplyFraction_spec_native
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T14:52:31.521727+00:00
-- url     : https://prove2.me/theorems/a302ff72-10e4-41d4-802a-c710f3eefda1
-- title:
--   Bounded execution of signed rational multiplication
-- statement:
--   Let $x_i=(-1)^{s_i}n_i/d_i$, where $s_i\le1$, $n_i,d_i\le M$ and $d_i>0$. Assume $2M^2+3<B$ and that the operand registers contain these signed fractions. The fixed command returns a reduced representation of the exact result in at most $36\operatorname{size}(d_1d_2)+64$ instructions:
--
--   $$x_{\rm out}=x_1\cdotx_2.$$
--
--   This is a reusable source interface for composing the complete finite-program implementation.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamRational.lean, theorem multiplyFraction_spec (lines 108–136)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
namespace Lax109476Proofs.RamRational
end Lax109476Proofs.RamRational

theorem Lax109476Proofs.RamRational.multiplyFraction_spec_native : ∀ (B M s₁ n₁ d₁ s₂ n₂ d₂ : Nat),
  @LT.lt Nat instLTNat
      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
            (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
        (@OfNat.ofNat Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      B →
    @LE.le Nat instLENat s₁ (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
      @LE.le Nat instLENat s₂ (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) →
        @LE.le Nat instLENat n₁ M →
          @LE.le Nat instLENat d₁ M →
            @LE.le Nat instLENat n₂ M →
              @LE.le Nat instLENat d₂ M →
                @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d₁ →
                  @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) d₂ →
                    Lax808846Proofs.Reasoning.Spec B (Lax109476Proofs.RamRational.fractionInputs s₁ n₁ d₁ s₂ n₂ d₂)
                      Lax109476Proofs.RamRational.multiplyFraction
                      (fun (x σ' : Lax808846Proofs.Imp.Env) =>
                        Lax109476Proofs.RamRational.FractionOutput
                          (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                            (Lax109476Proofs.RamRational.fractionValue s₁ n₁ d₁)
                            (Lax109476Proofs.RamRational.fractionValue s₂ n₂ d₂))
                          σ')
                      (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat)
                        (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                          (@OfNat.ofNat Nat (nat_lit 36) (instOfNatNat (nat_lit 36)))
                          (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) d₁ d₂).size)
                        (@OfNat.ofNat Nat (nat_lit 64) (instOfNatNat (nat_lit 64)))) := by sorry
